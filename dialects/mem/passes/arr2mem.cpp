#include "dialects/mem/passes/arr2mem.h"

#include <cstddef>

#include <deque>
#include <fstream>
#include <iterator>
#include <ranges>
#include <sstream>
#include <utility>

#include "thorin/def.h"
#include "thorin/lam.h"
#include "thorin/rewrite.h"
#include "thorin/tuple.h"
#include "thorin/world.h"

#include "thorin/be/dot/dot.h"
#include "thorin/pass/rw/lam_spec.h"
#include "thorin/pass/rw/scalarize.h"
#include "thorin/util/assert.h"
#include "thorin/util/dl.h"
#include "thorin/util/print.h"

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "dialects/core/core.h"
#include "dialects/direct/direct.h"
#include "dialects/mem/mem.h"
#include "dialects/mem/passes/fp/copy_prop.h"

namespace thorin::mem {

static std::pair<const App*, Array<Lam*>> isa_apped_nom_lam_in_tuple(const Def* def) {
    if (auto app = def->isa<App>()) {
        std::vector<Lam*> lams;
        std::deque<const Def*> wl;
        wl.push_back(app->callee());
        while (!wl.empty()) {
            auto elem = wl.front();
            wl.pop_front();
            if (auto nom = elem->isa_nom<Lam>()) {
                lams.push_back(nom);
            } else if (auto extract = elem->isa<Extract>()) {
                if (auto tuple = extract->tuple()->isa<Tuple>()) {
                    for (auto&& op : tuple->ops()) wl.push_back(op);
                } else {
                    return {nullptr, {}};
                }
            } else {
                return {nullptr, {}};
            }
        }
        return {app, lams};
    }
    return {nullptr, {}};
}

// @pre isa_apped_nom_lam_in_tuple(def) valid
template<class F, class H>
static const Def* rewrite_nom_lam_in_tuple(const Def* def, F&& rewrite, H&& rewrite_idx) {
    auto& w = def->world();
    if (auto nom = def->isa_nom<Lam>()) { return std::forward<F>(rewrite)(nom); }

    auto extract = def->as<Extract>();
    auto tuple   = extract->tuple()->as<Tuple>();
    DefArray new_ops{tuple->ops(), [&](const Def* op) {
                         return rewrite_nom_lam_in_tuple(op, std::forward<F>(rewrite), std::forward<H>(rewrite_idx));
                     }};
    return w.extract(w.tuple(new_ops, tuple->dbg()), rewrite_idx(extract->index()), extract->dbg());
}

// @pre isa_apped_nom_lam_in_tuple(def) valid
template<class RewriteCallee, class RewriteArg, class RewriteIdx>
static const Def* rewrite_apped_nom_lam_in_tuple(const Def* def,
                                                 RewriteCallee&& rewrite_callee,
                                                 RewriteArg&& rewrite_arg,
                                                 RewriteIdx&& rewrite_idx) {
    auto& w     = def->world();
    auto app    = def->as<App>();
    auto callee = rewrite_nom_lam_in_tuple(app->callee(), std::forward<RewriteCallee>(rewrite_callee),
                                           std::forward<RewriteIdx>(rewrite_idx));
    auto arg    = std::forward<RewriteArg>(rewrite_arg)(app->arg());
    return app->rebuild(w, app->type(), {callee, arg}, app->dbg());
}

void Arr2Mem::run() {
    world_.DLOG("===== Arr2Mem: Start =====");
    world_.debug_dump();

    rewritten_.clear();
    noms_.clear();

    auto noms = world_.externals() |
                std::views::transform([](auto external) { return external.second->template as_nom<Lam>(); });
    noms_ = std::vector<Lam*>{noms.begin(), noms.end()};
    while (!noms_.empty()) {
        auto nom = noms_.back();
        noms_.pop_back();

        { // assume externals have mem..
            Scope scope{nom};
            Scheduler sched{scope};
            std::swap(sched, scheduler_);

            val2mem_[nom] = mem::mem_var(nom);
            nom->set_body(add_mem_to_lams(nom, nom->body()));
        }
        // nom->dump(50);

        Scope scope{nom};
        Scheduler sched{scope};
        std::swap(sched, scheduler_);

        rewritten_[nom]        = nom;
        rewritten_[nom->var()] = nom->var();
        for (size_t i = 0, n = nom->num_ops(); i < n; ++i) static_cast<Def*>(nom)->set(i, rewrite(nom, nom->op(i)));
        // nom->dump(50);
    }
    world_.debug_dump();
    world_.DLOG("===== Arr2Mem: Done =====");
}

const Def* isa_dependent_array(const Def* def) {
    const Def* grp = nullptr;
    if (auto arr = def->isa<Arr>()) {
        if (arr->shape()->isa<Lit>() || arr->type()->isa<Type>())
            return nullptr;
        else
            grp = arr;
    }

    if (auto pack = def->isa<Pack>()) {
        if (pack->shape()->isa<Lit>() || pack->type()->isa<Type>())
            return nullptr;
        else
            grp = pack;
    }
    return grp;
}

const Def* isa_dependent_array_type(const Def* def) {
    const Def* grp = nullptr;
    if (auto arr = def->isa<Arr>()) {
        if (arr->shape()->isa<Lit>())
            return nullptr;
        else
            grp = arr;
    }

    if (auto pack = def->isa<Pack>()) {
        if (pack->shape()->isa<Lit>())
            return nullptr;
        else
            grp = pack;
    }
    return grp;
}

const Def* Arr2Mem::rewrite(Lam* nom) {
    if (!isa_workable(nom)) return nom; // e.g. imports

    if (auto new_def = rewritten_.find(nom); new_def != rewritten_.end()) { return new_def->second; }

    world_.DLOG("rewrite {}", nom);

    auto new_nom = nom->stub(world_, rewrite(nom, nom->type()), nom->dbg());

    // anti-recursion loop of death
    rewritten_[nom] = new_nom;
    // rewritten_[nom->var()] = new_nom->var();

    DefArray new_ops(nom->num_ops(), [&](size_t i) { return rewrite(nom, nom->op(i)); });

    new_nom->set(new_ops);

    return rewritten_[new_nom] = rewritten_[nom] = new_nom;
}

static const Def* follow_mem(const Def2Def& val2mem, const Def* mem) {
    auto it = val2mem.find(mem);
    while (it != val2mem.end()) {
        mem = it->second;
        it  = val2mem.find(mem);
    }
    return mem;
}

static const Def* array_fill(World& w, const Def* dst_mem, const Def* dst, const Def* val, const Def* size) {
    auto fill_wrap = w.nom_lam(w.cn({mem::type_mem(w), w.cn(mem::type_mem(w))}), w.dbg("fill_wrap"));
    auto fill      = w.nom_lam(w.cn({mem::type_mem(w), w.type_idx(0_s)}), w.dbg("fill"));
    auto brk       = w.nom_lam(w.cn(mem::type_mem(w)), nullptr);
    auto cnt       = w.nom_lam(w.cn(mem::type_mem(w)), nullptr);

    {
        auto [mem, i] = fill->vars<2>();

        auto lea_dst   = mem::op_lea(dst, core::op(core::conv::u2u, w.type_idx(size), i));
        auto store_mem = mem::op_store(mem, lea_dst, val);

        auto inc = core::op(core::wrap::add, core::Mode::none, i, w.lit(i->type(), 1));
        fill->branch(w.lit_ff(), core::op(core::icmp::ul, inc, core::op_bitcast(i->type(), size)), cnt, brk, store_mem);

        {
            auto mem = cnt->var();
            cnt->app(w.lit_ff(), fill, {mem, inc});
        }
        {
            auto mem = brk->var();
            brk->app(w.lit_ff(), fill_wrap->var(1), mem);
        }
    }
    fill_wrap->app(false, fill, {fill_wrap->var(0_s), w.lit(w.type_idx(0_s), 0)});

    auto ds_app = w.app(
        w.app(w.ax<direct::cps2ds>(), {fill_wrap->type()->dom(0_s), fill_wrap->type()->dom(1_s)->as<Pi>()->dom()}),
        fill_wrap);
    return w.app(ds_app, dst_mem);
}

static const Def* array_copy(World& w, const Def* src_mem, const Def* src, const Def* size) {
    auto [mem, dst] = mem::op_malloc(match<mem::Ptr, false>(src->type())->arg(0), src_mem)->projs<2>();

    auto copy_wrap = w.nom_lam(w.cn({mem::type_mem(w), w.cn({mem::type_mem(w), dst->type()})}), nullptr);
    auto copy      = w.nom_lam(w.cn({mem::type_mem(w), w.type_idx(0_s)}), w.dbg("copy"));
    auto brk       = w.nom_lam(w.cn(mem::type_mem(w)), nullptr);
    auto cnt       = w.nom_lam(w.cn(mem::type_mem(w)), nullptr);
    {
        auto [mem, i] = copy->vars<2>();

        auto idx             = core::op(core::conv::u2u, w.type_idx(size), i);
        auto lea_src         = mem::op_lea(src, idx);
        auto [load_mem, val] = mem::op_load(mem, lea_src)->projs<2>();
        mem                  = load_mem;

        auto lea_dst   = mem::op_lea(dst, idx);
        auto store_mem = mem::op_store(load_mem, lea_dst, val);

        auto inc = core::op(core::wrap::add, core::Mode::none, i, w.lit(i->type(), 1));
        copy->branch(w.lit_ff(), core::op(core::icmp::ul, inc, core::op_bitcast(i->type(), size)), cnt, brk, store_mem);

        {
            auto mem = cnt->var();
            cnt->app(w.lit_ff(), copy, {mem, inc});
        }
        {
            auto mem = brk->var();
            brk->app(false, copy_wrap->var(1), {mem, dst});
            brk->set_filter(w.lit_ff());
        }
    }
    copy_wrap->app(false, copy, {copy_wrap->var(0_s), w.lit(w.type_idx(0_s), 0)});

    auto ds_app = w.app(
        w.app(w.ax<direct::cps2ds>(), {copy_wrap->type()->dom(0_s), copy_wrap->type()->dom(1_s)->as<Pi>()->dom()}),
        copy_wrap);
    return w.app(ds_app, mem);
}

const Def* Arr2Mem::rewrite(Lam*& curr_nom, const Def* def) {
    if (!def) return nullptr;
    if (auto new_def = rewritten_.find(def); new_def != rewritten_.end()) {
        // need new malloc each time..
        if (!(isa_dependent_array(def) && def->num_uses() > 1)) return new_def->second;
    }
    if (def->dep_none()) return def;
    if (auto nom = def->isa_nom<Lam>()) { return rewrite(nom); }

    // def->dump(0);
    auto new_type = rewrite(curr_nom, def->type());

    if (auto old_nom = def->isa_nom(); old_nom && old_nom != curr_nom) {
        auto new_nom        = old_nom->stub(world_, new_type, def->dbg());
        rewritten_[new_nom] = rewritten_[old_nom] = new_nom;
        // rewritten_[old_nom->var()] = new_nom->var();

        for (size_t i = 0, e = old_nom->num_ops(); i != e; ++i) {
            if (auto old_op = old_nom->op(i)) new_nom->set(i, rewrite(curr_nom, old_op));
        }

        if (auto new_def = new_nom->restructure()) return rewritten_[new_nom] = rewritten_[old_nom] = new_def;

        return new_nom;
    }

    auto mem_var = [&]() -> const Def* {
        auto place = static_cast<Lam*>(scheduler_.smart(def));
        if (auto mem_var = mem::mem_var(place)) return mem_var;
        if (auto it = val2mem_.find(place); it != val2mem_.end()) return it->second;
        unreachable();
        return nullptr;
    };

    if (auto grp = isa_dependent_array(def)) {
        // todo: mem?!
        auto nom_mem  = mem_var();
        auto mem      = follow_mem(val2mem_, rewrite(curr_nom, nom_mem));
        auto ptr_type = rewrite(curr_nom, grp->type());
        auto arr_type = match<mem::Ptr, false>(ptr_type)->arg(0);
        auto alloc    = mem::op_malloc(arr_type, mem);

        auto [new_mem, ptr] = alloc->projs<2>();
        new_mem             = array_fill(world_, new_mem, ptr, rewrite(curr_nom, grp->as<Pack>()->body()),
                                         rewrite(curr_nom, grp->arity()));

        world_.DLOG("dump after arr fill");
        // new_mem->dump(5);
        assert(match<mem::M>(new_mem->type()));
        val2mem_.emplace(grp, new_mem);
        val2mem_.emplace(ptr, new_mem);
        val2mem_[mem]       = new_mem;
        rewritten_[nom_mem] = new_mem;

        // alloc->dump(0);
        return rewritten_[def] = ptr;
    }

    if (auto ptr = match<mem::Ptr>(def)) {
        if (auto arr = isa_dependent_array_type(ptr->arg(0))) {
            DefArray new_arr_ops{arr->num_ops(), [&](size_t i) { return rewrite(curr_nom, arr->op(i)); }};
            auto new_arr =
                arr->rebuild(world_, rewrite(curr_nom, arr->type()), new_arr_ops, rewrite(curr_nom, arr->dbg()));
            return rewritten_[ptr] = ptr->rebuild(
                       world_, rewrite(curr_nom, ptr->type()),
                       {ptr->axiom(), world_.tuple({new_arr, rewrite(curr_nom, ptr->arg(1))})}, ptr->dbg());
        }
    }

    if (auto lea = match<mem::lea>(def)) {
        auto typed_lea = lea->callee()->as<App>();

        if (auto arr = isa_dependent_array_type(typed_lea->arg(1))) {
            auto new_array_type = rewrite(curr_nom, arr->type());

            DefArray new_arr_ops{arr->num_ops(), [&](size_t i) { return rewrite(curr_nom, arr->op(i)); }};
            auto new_arr       = arr->rebuild(world_, new_array_type, new_arr_ops, rewrite(curr_nom, arr->dbg()));
            auto new_typed_lea = rewritten_[typed_lea] = typed_lea->rebuild(
                world_, rewrite(curr_nom, typed_lea->type()),
                {lea->axiom(),
                 world_.tuple({rewrite(curr_nom, typed_lea->arg(0)), new_arr, rewrite(curr_nom, typed_lea->arg(2))})},
                typed_lea->dbg());

            auto new_arg           = rewrite(curr_nom, lea->arg());
            return rewritten_[lea] = world_.app(new_typed_lea, new_arg, lea->dbg());
        }
    }

    // todo: malloc / (m)slot?
    if (auto alloc = match<mem::alloc>(def)) {
        auto typed_alloc = alloc->callee()->as<App>();
        if (auto arr = isa_dependent_array_type(typed_alloc->arg(0))) {
            DefArray new_arr_ops{arr->num_ops(), [&](size_t i) { return rewrite(curr_nom, arr->op(i)); }};
            auto new_arr =
                arr->rebuild(world_, rewrite(curr_nom, arr->type()), new_arr_ops, rewrite(curr_nom, arr->dbg()));
            rewritten_[typed_alloc] = typed_alloc->rebuild(
                world_, rewrite(curr_nom, typed_alloc->type()),
                {typed_alloc->axiom(), world_.tuple({new_arr, rewrite(curr_nom, typed_alloc->arg(1))})},
                typed_alloc->dbg());
        }
    }

    if (auto arr = isa_dependent_array_type(def)) {
        DefArray new_ops{arr->num_ops(), [&](size_t i) { return rewrite(curr_nom, arr->op(i)); }};
        auto new_arr = arr->rebuild(world_, rewrite(curr_nom, arr->type()), new_ops, rewrite(curr_nom, arr->dbg()));

        auto ptr = mem::type_ptr(new_arr);
        // std::cout << "type: ";
        // arr->dump(0);
        // ptr->dump(0);
        rewritten_[ptr]        = ptr;
        return rewritten_[def] = ptr;
    }

    auto update_val2mem = [this](const Def* new_mem, auto... ops) {
        assert(match<mem::M>(new_mem->type()));
        (val2mem_[ops] = ... = new_mem);
    };

    if (auto extract = def->isa<Extract>()) {
        // extract->dump();
        auto tuple = extract->tuple();
        if (auto arr = isa_dependent_array_type(tuple->type())) {
            auto ptr = rewrite(curr_nom, tuple);
            auto lea = mem::op_lea(ptr, rewrite(curr_nom, extract->index()));

            auto nom_mem            = mem_var();
            auto old_mem            = follow_mem(val2mem_, rewrite(curr_nom, nom_mem));
            auto [new_mem, new_val] = mem::op_load(old_mem, lea)->projs<2>();

            assert(new_mem);

            update_val2mem(new_mem, arr, ptr, old_mem, rewritten_[nom_mem]);
            world_.DLOG("load mem {} -> {}, followed: {}", old_mem, new_mem, follow_mem(val2mem_, old_mem));

            return rewritten_[def] = new_val;
        }
    }

    if (auto insert = def->isa<Insert>()) {
        // insert->dump();
        auto tuple = insert->tuple();
        if (auto arr = isa_dependent_array_type(tuple->type())) {
            auto ptr            = rewrite(curr_nom, tuple);
            auto nom_mem        = mem_var();
            auto old_mem        = follow_mem(val2mem_, rewrite(curr_nom, nom_mem));
            auto [mem, dst_ptr] = array_copy(world_, old_mem, ptr, rewrite(curr_nom, arr->arity()))->projs<2>();

            world_.DLOG("dump after arr copy");
            // mem->dump(5);
            auto lea     = mem::op_lea(dst_ptr, rewrite(curr_nom, insert->index()));
            auto new_mem = mem::op_store(mem, lea, rewrite(curr_nom, insert->value()));
            assert(new_mem);

            update_val2mem(new_mem, arr, ptr, dst_ptr, old_mem, rewritten_[nom_mem]);

            return rewritten_[def] = dst_ptr;
        }
    }

    DefArray ops{def->num_ops(), [def, &curr_nom, this](size_t i) { return rewrite(curr_nom, def->op(i)); }};
    if (auto app = def->isa<App>()) {
        if (app->num_args() > 0 && match<mem::M>(app->arg(0)->type())) {
            // todo: bit cheesy..
            auto args = ops[1];
            DefArray new_args(args->num_ops(), [&](size_t i) {
                if (i == 0) return follow_mem(val2mem_, args->op(0));
                return args->op(i);
            });
            ops[1] = args->rebuild(world_, args->type(), new_args, args->dbg());
        }
    }

    auto new_def = def->rebuild(world_, new_type, ops, def->dbg());

    return rewritten_[def] = new_def;
}

const Def* Arr2Mem::add_mem_to_lams(Lam* curr_lam, const Def* def) {
    auto place   = static_cast<Lam*>(scheduler_.smart(def));
    auto mem_var = [&](Lam* nom) -> const Def* {
        world_.DLOG("get mem_var for {}", nom);
        if (auto mem_var = mem::mem_var(nom)) return mem_var;
        if (auto it = val2mem_.find(nom); it != val2mem_.end()) return it->second;
        unreachable();
        return nullptr;
    };

    world_.DLOG("rewriting {} in {}", def, place);

    if (auto nom_lam = def->isa_nom<Lam>(); nom_lam && !nom_lam->is_set()) return def;
    if (auto it = mem_rewritten_.find(def); it != mem_rewritten_.end()) {
        auto tmp = it->second;
        if (match<mem::M>(def->type())) {
            world_.DLOG("already known mem {} in {}", def, curr_lam);
            return follow_mem(val2mem_, mem_var(curr_lam));
        }
        return tmp;
    }
    if (match<mem::M>(def->type())) { world_.DLOG("new mem {} in {}", def, curr_lam); }

    // todo: do we need to stub noms ..?
    if (auto nom = def->isa_nom<Lam>()) {
        mem_rewritten_[nom] = nom;
        for (size_t i = 0, n = nom->num_ops(); i < n; ++i) {
            static_cast<Def*>(nom)->set(i, add_mem_to_lams(nom, nom->op(i)));
        }
        return nom;
    }
    assert(!def->isa_nom());

    if (auto apped_nom = isa_apped_nom_lam_in_tuple(def); apped_nom.first) {
        auto rewrite_arg = [&](const Def* arg) -> const Def* {
            if (arg->type()->num_projs() > 0 && match<mem::M>(arg->type()->proj(0)))
                return arg->rebuild(arg->world(), arg->type(),
                                    DefArray{arg->ops(), [&](const Def* op) { return add_mem_to_lams(place, op); }},
                                    arg->dbg());

            // return arg->rebuild(arg->world(), arg->type(),
            // DefArray{arg->ops(),
            //          [&](const Def* op) {
            //              if (match<mem::M>(op->type()))
            //                  return add_mem_to_lams(place,
            //                                         follow_mem(val2mem_, mem_var(place)));
            //              return add_mem_to_lams(place, op);
            //          }},
            // arg->dbg());

            if (arg->isa<Tuple>() || arg->isa<Arr>() || arg->isa<Pack>()) {
                DefArray new_args{arg->num_projs() + 1};
                for (int i = arg->num_projs(); i >= 0; i--) {
                    new_args[i] = i == 0 ? add_mem_to_lams(place, follow_mem(val2mem_, mem_var(place)))
                                         : add_mem_to_lams(place, arg->proj(i - 1));
                }
                return arg->world().tuple(new_args, arg->dbg());
            }

            return arg->world().tuple(
                {add_mem_to_lams(place, follow_mem(val2mem_, mem_var(place))), add_mem_to_lams(place, arg)},
                arg->dbg());
        };

        auto rewrite_lam = [&](Lam* nom) -> const Def* {
            if (auto it = mem_rewritten_.find(nom); it != mem_rewritten_.end())
                if (auto pi = it->second->type()->as<Pi>(); pi->num_doms() > 0 && match<mem::M>(pi->dom(0_s)))
                    return it->second;
            if (auto pi = nom->type()->as<Pi>(); pi->num_doms() > 0 && match<mem::M>(pi->dom(0_s)))
                return add_mem_to_lams(place, nom);

            auto pi            = nom->type()->as<Pi>();
            auto dom           = pi->dom();
            const Def* new_dom = nullptr;
            if (dom->isa<Sigma>() || dom->isa<Arr>() || dom->isa<Pack>()) { // what about packs / arrays..?
                new_dom = world_.sigma(DefArray{
                    dom->num_projs() + 1, [&](size_t i) { return i == 0 ? mem::type_mem(world_) : dom->proj(i - 1); }});
            } else {
                new_dom = world_.sigma({mem::type_mem(world_), dom});
            }

            auto new_nom = nom->stub(world_, world_.pi(new_dom, pi->codom()), nom->dbg());

            for (size_t i = 0; i < nom->num_vars(); ++i) mem_rewritten_[nom->var(i)] = new_nom->var(i + 1);
            if (nom->num_vars() > 1) mem_rewritten_[nom->var()] = new_nom->var();

            mem_rewritten_[new_nom] = new_nom;
            mem_rewritten_[nom]     = new_nom;
            val2mem_[new_nom]       = new_nom->var(0_s);
            val2mem_[nom]           = new_nom->var(0_s);

            new_nom->set(add_mem_to_lams(place, nom->filter()), add_mem_to_lams(place, nom->body()));
            return new_nom;
        };

        return mem_rewritten_[def] =
                   rewrite_apped_nom_lam_in_tuple(def, rewrite_lam, std::move(rewrite_arg),
                                                  [&](const Def* def) { return add_mem_to_lams(place, def); });
    }

    DefArray new_ops{def->ops(), [&](const Def* op) { return add_mem_to_lams(place, op); }};

    auto tmp = mem_rewritten_[def] = def->rebuild(world_, def->type(), new_ops, def->dbg());
    return tmp;
}

const Def* var_for_call(const Def* val, const App* call) {
    auto num_args = call->arg()->num_ops();
    for (size_t i = 0; i < num_args; ++i) {
        if (call->arg(i) == val) return call->callee()->proj(i);
    }
    return nullptr;
}

struct ArrGraph {
    struct ArrNode {
        explicit ArrNode(const Def* d)
            : def_(d) {}

        std::string name() const { return def_->unique_name(); }
        const Def* def() const { return def_; }

        void add_child(ArrNode* child) { refs_.emplace(child); }

        auto begin() const { return refs_.cbegin(); }

        auto end() const { return refs_.cend(); }

    private:
        struct ArrNodeHash {
            size_t operator()(ArrNode* p) const { return p->def_->hash(); };
        };

        struct ArrNodeEq {
            bool operator()(ArrNode* a, ArrNode* b) const { return a == b; }
        };
        const Def* def_;
        absl::flat_hash_set<ArrNode*, ArrNodeHash, ArrNodeEq> refs_;
    };

    ArrNode* insert(const Def* d) {
        if (auto it = def2node_.find(d); it != def2node_.end()) return it->second;
        auto& ptr = nodes_.emplace_back(new ArrNode(d));
        def2node_.emplace(d, ptr.get());
        return ptr.get();
    }

    auto begin() const { return nodes_.cbegin(); }

    auto end() const { return nodes_.cend(); }

private:
    DefMap<ArrNode*> def2node_;
    std::vector<std::unique_ptr<ArrNode>> nodes_;
};

struct UnionFind {
    void insert(const Def* def, const Def* def_onion) {
        auto insert_to_onion = [this, def](DefSet* onion) {
            if (auto def_union_it = def2union_.find(def); def_union_it != def2union_.end()) {
                for (auto d : *def_union_it->second) {
                    def2union_.at(d) = onion;
                    onion->insert(d);
                }
                // todo: in theory we could deallocate the old DefSet now.
                // would remove the need for UnionIterator::next_valid
            } else {
                def2union_.emplace(def, onion);
                onion->insert(def);
            }
        };

        if (auto it = def2union_.find(def_onion); it != def2union_.end()) {
            insert_to_onion(it->second);
        } else {
            auto new_union = unions_.emplace_back(new DefSet()).get();
            insert_to_onion(new_union);
            if (def_onion != def) {
                new_union->insert(def_onion);
                def2union_.emplace(def_onion, new_union);
            }
        }
    }

    const DefSet* find(const Def* def) const {
        if (auto it = def2union_.find(def); it != def2union_.end()) return it->second;
        return nullptr;
    }

    struct UnionIterator {
        using value_type = const DefSet*;
        using reference  = const DefSet*;

        UnionIterator()
            : it_()
            , uf_(nullptr) {}

        explicit UnionIterator(const UnionFind& find)
            : it_(find.unions_.begin())
            , uf_(&find) {
            next_valid();
        }

        UnionIterator operator++() {
            if (uf_) {
                it_++;
                next_valid();
            }
            return *this;
        }

        reference operator*() { return it_->get(); }

        friend bool operator!=(const UnionIterator& lhs, const UnionIterator& rhs) { return lhs.it_ != rhs.it_; }

    private:
        using wrapped_iterator = std::vector<std::unique_ptr<DefSet>>::const_iterator;

        void next_valid() {
            while (it_ != uf_->unions_.end() && uf_->find(*it_->get()->begin()) != it_->get()) it_++;
            if (it_ == uf_->unions_.end()) it_ = {};
        }

        std::vector<std::unique_ptr<DefSet>>::const_iterator it_;
        const UnionFind* uf_;
    };

    UnionIterator begin() const { return UnionIterator{*this}; }
    UnionIterator end() const { return {}; }

private:
    DefMap<DefSet*> def2union_;
    std::vector<std::unique_ptr<DefSet>> unions_;
};

class ArrAna {
public:
    ArrAna(World& world)
        : world_(world) {}

    void analyze();
    void print(std::ostream& os) const;

    const DefSet* phi_web(const Def* from) const;

private:
    bool analyze_union(const Def*);
    ArrGraph::ArrNode* analyze(const Def*);
    void print(std::ostream& os,
               const ArrGraph::ArrNode* node,
               absl::flat_hash_set<const ArrGraph::ArrNode*>& printedNodes) const;
    void print_union(std::ostream& os, const DefSet& onion) const;

    void print(std::ostream& os, const Def* d) const;
    void print(std::ostream& os, const Def* d0, const Def* d1) const;

    World& world_;
    DefMap<ArrGraph::ArrNode*> cache_;
    ArrGraph graph_;
    DefSet visited_;
    UnionFind union_find_;
};

bool ArrAna::analyze_union(const Def* def) {
    if (def == nullptr) return false;
    if (visited_.contains(def)) return union_find_.find(def);

    if (auto ex = def->isa<Extract>(); ex && !ex->tuple()->arity()->isa<Lit>()) {
        union_find_.insert(def, ex->tuple());
    } else if (auto in = def->isa<Insert>(); in && !in->tuple()->arity()->isa<Lit>()) {
        union_find_.insert(def, in->tuple());
    } else if (isa_dependent_array(def)) {
        union_find_.insert(def, def);
    } else if (isa_dependent_array_type(def->type())) {
        union_find_.insert(def, def);
    } else if (auto [app, lams] = isa_apped_nom_lam_in_tuple(def);
               app && std::ranges::any_of(lams[0]->dom()->ops(), isa_dependent_array_type)) {
        // add phis
        for (size_t i = 0, e = app->num_args(); i < e; ++i)
            if (analyze_union(app->arg(i)))
                for (auto lam : lams)
                    if (analyze_union(lam->var(i))) union_find_.insert(app->arg(i), lam->var(i));
    }
    visited_.insert(def);

    for (const auto* op : def->ops())
        if (analyze_union(op) && union_find_.find(def)) union_find_.insert(op, def);

    return union_find_.find(def);
}

ArrGraph::ArrNode* ArrAna::analyze(const Def* def) {
    if (def == nullptr) return nullptr;
    if (auto it = cache_.find(def); it != cache_.end()) return it->second;

    ArrGraph::ArrNode* node = nullptr;
    if (auto ex = def->isa<Extract>(); ex && !ex->tuple()->arity()->isa<Lit>()) {
        node = graph_.insert(ex);
        node->add_child(graph_.insert(ex->tuple()));
    } else if (auto in = def->isa<Insert>(); in && !in->tuple()->arity()->isa<Lit>()) {
        node = graph_.insert(in);
        node->add_child(graph_.insert(in->tuple()));
    } else if (isa_dependent_array(def)) {
        node = graph_.insert(def);
    } else if (isa_dependent_array_type(def->type())) {
        node = graph_.insert(def);
    } else if (auto [app, lams] = isa_apped_nom_lam_in_tuple(def);
               app && std::ranges::any_of(lams[0]->dom()->ops(), isa_dependent_array_type)) {
        // add phis
        for (size_t i = 0, e = app->num_args(); i < e; ++i)
            if (auto node = analyze(app->arg(i)))
                for (auto lam : lams)
                    if (auto dep = analyze(lam->var(i))) dep->add_child(node);
    }

    cache_.emplace(def, node);
    for (const auto* op : def->ops())
        if (auto dep = analyze(op); dep && node) node->add_child(dep);

    return node;
}

void ArrAna::analyze() {
    cache_.clear();
    graph_ = ArrGraph{};

    auto noms = world_.externals() |
                std::ranges::views::transform([](auto external) { return external.second->template as_nom<Lam>(); });
    for (auto nom : noms) {
        for (auto& op : nom->ops()) analyze_union(op);
        // for (auto& op : nom->ops()) analyze(op);
    }
}

const DefSet* ArrAna::phi_web(const Def* from) const { return union_find_.find(from); }

void ArrAna::print(std::ostream& os) const {
    absl::flat_hash_set<const ArrGraph::ArrNode*> printedNodes;

    os << "digraph Arr {\n";
    // for (auto& node : graph_) { print(os, node.get(), printedNodes); }
    for (auto onion : union_find_) print_union(os, *onion);
    os << "}" << std::endl;
}

void ArrAna::print(std::ostream& os,
                   const ArrGraph::ArrNode* node,
                   absl::flat_hash_set<const ArrGraph::ArrNode*>& printedNodes) const {
    if (!printedNodes.emplace(node).second) return;

    print(os, node->def());

    for (auto* child : *node) {
        print(os, child, printedNodes);
        print(os, node->def(), child->def());
    }
}

void ArrAna::print_union(std::ostream& os, const DefSet& onion) const {
    for (auto def : onion) {
        print(os, def);
        if (def != *onion.begin()) print(os, def, *onion.begin());
    }
}

void ArrAna::print(std::ostream& os, const Def* d) const {
    os << "\"" << d->unique_name() << "\" [label=\"";
    { // skip new-line
        std::stringstream ss;
        d->stream(ss, 0);
        std::string str{ss.str()};
        os << std::string{++str.cbegin(), str.cend()};
    }
    if (d->isa<Var>() || (d->isa<Extract>() && d->op(0)->isa<Var>() && isa_lit(d->op(0)->arity())))
        os << "\", color=red];\n";
    else if (!d->isa<Extract>() && !d->isa<Insert>())
        os << "\", color=blue, shape=rect];\n";
    else if (!d->isa<Extract>())
        os << "\", color=darkorchid, shape=rect];\n";
    else
        os << "\", shape=rect];\n";
}
void ArrAna::print(std::ostream& os, const Def* d0, const Def* d1) const {
    os << "\"" << d1->unique_name() << "\" -> \"" << d0->unique_name() << "\";\n";
}

void arr2mem(World& w) {
    ArrAna aana{w};
    aana.analyze();
    std::ofstream fana{"arrana.dot"};
    aana.print(fana);

    Arr2Mem a2m{w};
    a2m.run();

    auto direct = Dialect::load("direct", {});
    PassMan man{w};
    auto add_ds2cps = reinterpret_cast<decltype(&direct::thorin_add_direct_ds2cps)>(
        dl::get(direct.handle(), "thorin_add_direct_ds2cps"));
    add_ds2cps(man);
    man.run();
    PassMan::run<LamSpec>(w);
}
} // namespace thorin::mem
