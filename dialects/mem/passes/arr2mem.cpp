#include "dialects/mem/passes/arr2mem.h"

#include <deque>
#include <fstream>
#include <iterator>
#include <ranges>

#include "thorin/def.h"
#include "thorin/lam.h"
#include "thorin/rewrite.h"
#include "thorin/tables.h"
#include "thorin/tuple.h"
#include "thorin/world.h"

#include "thorin/be/dot/dot.h"
#include "thorin/pass/rw/lam_spec.h"
#include "thorin/util/dl.h"
#include "thorin/util/print.h"

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "dialects/core/core.h"
#include "dialects/direct/direct.h"
#include "dialects/mem/mem.h"
#include "dialects/mem/passes/fp/copy_prop.h"

namespace thorin::mem {

void Arr2Mem::run() {
    world_.DLOG("===== Arr2Mem: Start =====");

    rewritten_.clear();
    noms_.clear();

    auto noms = world_.externals() |
                std::views::transform([](auto external) { return external.second->template as_nom<Lam>(); });
    noms_ = std::vector<Lam*>{noms.begin(), noms.end()};
    while (!noms_.empty()) {
        auto nom = noms_.back();
        noms_.pop_back();

        rewritten_[nom]        = nom;
        rewritten_[nom->var()] = nom->var();
        for (size_t i = 0, n = nom->num_ops(); i < n; ++i) static_cast<Def*>(nom)->set(i, rewrite(nom, nom->op(i)));

        // nom->dump(10);
    }
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
    auto fill_wrap = w.nom_lam(w.cn({mem::type_mem(w), w.cn(mem::type_mem(w))}), w.dbg("fill"));
    auto fill      = w.nom_lam(w.cn({mem::type_mem(w), w.type_int(0_s)}), w.dbg("fill"));
    auto brk       = w.nom_lam(w.cn(mem::type_mem(w)), nullptr);
    auto cnt       = w.nom_lam(w.cn(mem::type_mem(w)), nullptr);

    {
        auto [mem, i] = fill->vars<2>();

        auto lea_dst   = mem::op_lea(dst, core::op(core::conv::u2u, w.type_int(size), i));
        auto store_mem = mem::op_store(mem, lea_dst, val);

        auto inc = core::op(core::wrap::add, WMode::none, i, w.lit_int(i->type(), 1));
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
    fill_wrap->app(false, fill, {fill_wrap->var(0_s), w.lit(w.type_int(0_s), 0)});

    auto ds_app = w.app(
        w.app(w.ax<direct::cps2ds>(), {fill_wrap->type()->dom(0_s), fill_wrap->type()->dom(1_s)->as<Pi>()->dom()}),
        fill_wrap);
    return w.app(ds_app, dst_mem);
}

static const Def* array_copy(World& w, const Def* src_mem, const Def* src, const Def* size) {
    auto [mem, dst] = mem::op_malloc(match<mem::Ptr, false>(src->type())->arg(0), src_mem)->projs<2>();

    auto copy_wrap = w.nom_lam(w.cn({mem::type_mem(w), w.cn({mem::type_mem(w), dst->type()})}), nullptr);
    auto copy      = w.nom_lam(w.cn({mem::type_mem(w), w.type_int(0_s)}), w.dbg("copy"));
    auto brk       = w.nom_lam(w.cn(mem::type_mem(w)), nullptr);
    auto cnt       = w.nom_lam(w.cn(mem::type_mem(w)), nullptr);
    {
        auto [mem, i] = copy->vars<2>();

        auto idx             = core::op(core::conv::u2u, w.type_int(size), i);
        auto lea_src         = mem::op_lea(src, idx);
        auto [load_mem, val] = mem::op_load(mem, lea_src)->projs<2>();
        mem                  = load_mem;

        auto lea_dst   = mem::op_lea(dst, idx);
        auto store_mem = mem::op_store(load_mem, lea_dst, val);

        auto inc = core::op(core::wrap::add, WMode::none, i, w.lit_int(i->type(), 1));
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
    copy_wrap->app(false, copy, {copy_wrap->var(0_s), w.lit(w.type_int(0_s), 0)});

    auto ds_app = w.app(
        w.app(w.ax<direct::cps2ds>(), {copy_wrap->type()->dom(0_s), copy_wrap->type()->dom(1_s)->as<Pi>()->dom()}),
        copy_wrap);
    return w.app(ds_app, mem);
}

const Def* Arr2Mem::rewrite(Lam* curr_nom, const Def* def) {
    if (!def) return nullptr;
    if (auto new_def = rewritten_.find(def); new_def != rewritten_.end()) {
        return new_def->second;
        // if (def == new_def->second) return def;
        // return rewritten_[def] = rewrite(curr_nom, new_def->second);
    }
    if (def->no_dep()) return def;
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

    if (auto grp = isa_dependent_array(def)) {
        // todo: mem?!
        auto mem      = follow_mem(val2mem_, rewrite(curr_nom, mem::mem_var(curr_nom)));
        auto ptr_type = rewrite(curr_nom, grp->type());
        auto arr_type = match<mem::Ptr, false>(ptr_type)->arg(0);
        auto alloc    = mem::op_malloc(arr_type, mem);

        auto [new_mem, ptr] = alloc->projs<2>();
        new_mem             = array_fill(world_, new_mem, ptr, rewrite(curr_nom, grp->as<Pack>()->body()),
                                         rewrite(curr_nom, grp->arity()));

        assert(match<mem::M>(new_mem->type()));
        val2mem_.emplace(grp, new_mem);
        val2mem_.emplace(ptr, new_mem);
        val2mem_[mem]                      = new_mem;
        rewritten_[mem::mem_var(curr_nom)] = new_mem;

        // alloc->dump(0);
        return rewritten_[def] = ptr;
    }

    if (auto arr = isa_dependent_array_type(def)) {
        DefArray new_ops{arr->num_ops(), [&](size_t i) { return rewrite(curr_nom, arr->op(i)); }};
        auto new_arr = arr->rebuild(world_, rewrite(curr_nom, arr->type()), new_ops, rewrite(curr_nom, arr->dbg()));

        auto ptr = mem::type_ptr(new_arr);
        std::cout << "type: ";
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

            auto old_mem            = follow_mem(val2mem_, rewrite(curr_nom, mem::mem_var(curr_nom)));
            auto [new_mem, new_val] = mem::op_load(old_mem, lea)->projs<2>();

            assert(new_mem);

            update_val2mem(new_mem, arr, ptr, old_mem, rewritten_[mem::mem_var(curr_nom)]);
            world_.DLOG("load mem {} -> {}, followed: {}", old_mem, new_mem, follow_mem(val2mem_, old_mem));

            return rewritten_[def] = new_val;
        }
    }

    if (auto insert = def->isa<Insert>()) {
        // insert->dump();
        auto tuple = insert->tuple();
        if (auto arr = isa_dependent_array_type(tuple->type())) {
            auto ptr            = rewrite(curr_nom, tuple);
            auto old_mem        = follow_mem(val2mem_, rewrite(curr_nom, mem::mem_var(curr_nom)));
            auto [mem, dst_ptr] = array_copy(world_, old_mem, ptr, rewrite(curr_nom, arr->arity()))->projs<2>();
            world_.DLOG("dump after arr copy");
            // mem->dump(5);
            auto lea     = mem::op_lea(dst_ptr, rewrite(curr_nom, insert->index()));
            auto new_mem = mem::op_store(mem, lea, rewrite(curr_nom, insert->value()));
            assert(new_mem);

            update_val2mem(new_mem, arr, ptr, dst_ptr, old_mem, rewritten_[mem::mem_var(curr_nom)]);

            return rewritten_[def] = dst_ptr;
        }
    }

    DefArray ops{def->num_ops(), [def, curr_nom, this](size_t i) { return rewrite(curr_nom, def->op(i)); }};
    if (auto app = def->isa<App>()) {
        if (match<mem::M>(app->arg(0)->type())) {
            // todo: bit cheesy..
            auto args = ops[1];
            DefArray new_args(args->num_ops(), [&](size_t i) {
                if (i == 0) return follow_mem(val2mem_, args->op(0));
                return args->op(i);
            });
            // args->refine(0, follow_mem(val2mem_, args->op(0)));
            ops[1] = args->rebuild(world_, args->type(), new_args, args->dbg());
        }
    }

    auto new_def           = def->rebuild(world_, new_type, ops, def->dbg());
    return rewritten_[def] = new_def;
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

class ArrAna {
public:
    ArrAna(World& world)
        : world_(world) {}

    void analyze();
    void print(std::ostream& os) const;

private:
    ArrGraph::ArrNode* analyze(const Def*);
    void print(std::ostream& os, const ArrGraph::ArrNode* node) const;

    World& world_;
    DefMap<ArrGraph::ArrNode*> cache_;
    ArrGraph graph_;
    mutable absl::flat_hash_set<const ArrGraph::ArrNode*> printedNodes_;
};

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
        //     } else if (std::ranges::any_of(def->type()->ops(), isa_dependent_array_type)) {
        //         node = graph_.insert(def);
    } else if (auto [app, lam] = isa_apped_nom_lam(def);
               lam && std::ranges::any_of(lam->dom()->ops(), isa_dependent_array_type)) {
        for (size_t i = 0, e = app->num_args(); i < e; ++i) {
            if (auto node = analyze(app->arg(i))) {
                if (auto dep = analyze(lam->var(i))) dep->add_child(node);
            }
        }
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
        for (auto& op : nom->ops()) analyze(op);
    }
}

void ArrAna::print(std::ostream& os) const {
    printedNodes_.clear();

    os << "digraph Arr {\n";
    for (auto& node : graph_) { print(os, node.get()); }
    os << "}" << std::endl;
}

void ArrAna::print(std::ostream& os, const ArrGraph::ArrNode* node) const {
    if (!printedNodes_.emplace(node).second) return;

    os << "\"" << node->name() << "\" [label=\"";
    node->def()->stream(os, 0);
    // os << node->def();
    os << "\"];\n";
    for (auto* child : *node) {
        print(os, child);
        os << "\"" << node->name() << "\" -> \"" << child->name() << "\";\n";
    }
}

class PrintAna {
public:
    PrintAna(World& w)
        : world_(w) {}

    void analyze();

private:
    bool analyze(const Def*);

    World& world_;
    absl::flat_hash_set<const Def*> seen_;
    absl::flat_hash_set<const Def*> print_;
    std::vector<const Def*> noms_;
};

bool PrintAna::analyze(const Def* d) {
    if (print_.contains(d)) return true;
    if (seen_.contains(d)) return false;

    seen_.emplace(d);

    if (d->isa_nom()) {
        noms_.push_back(d);
        return false;
    }

    bool print = false;
    auto tbp   = [this, &print](auto def) {
        if (!print) print_.emplace(def);
        print |= true;
    };

    if (d->type() && analyze(d->type())) tbp(d);

    if (auto insert = d->isa<Insert>(); insert && !insert->tuple()->arity()->isa<Lit>())
        tbp(d);
    else if (auto extract = d->isa<Extract>()) {
        for (auto& op : d->ops()) analyze(op);
        if (!extract->tuple()->arity()->isa<Lit>()) tbp(d);
        return false;
    } else if (isa_dependent_array_type(d))
        tbp(d);

    for (auto& op : d->ops())
        if (analyze(op)) tbp(d);

    return print;
}

void PrintAna::analyze() {
    seen_.clear();
    noms_.clear();

    auto noms = world_.externals() |
                std::ranges::views::transform([](auto external) { return external.second->template as_nom<Lam>(); });
    noms_ = std::vector<const Def*>{noms.begin(), noms.end()};
    while (!noms_.empty()) {
        auto nom = noms_.back();
        noms_.pop_back();
        for (auto& op : nom->ops()) analyze(op);
    }

    std::ofstream f{"out.dot"};
    dot::emit(world_, f, [this](std::ostream& os, const Def* def) {
        if (print_.contains(def)) def->stream(os, 0);
    });
    std::ofstream fiearr{"iearr.dot"};
    dot::emit(world_, fiearr, [](std::ostream& os, const Def* def) {
        if (auto ex = def->isa<Extract>(); ex && !ex->tuple()->arity()->isa<Lit>())
            def->stream(os, 0);
        else if (auto in = def->isa<Insert>(); in && !in->tuple()->arity()->isa<Lit>())
            def->stream(os, 0);
        else if (isa_dependent_array_type(def))
            def->stream(os, 0);
        else if (isa_dependent_array_type(def->type()))
            def->stream(os, 0);
        else if (std::ranges::any_of(def->type()->ops(), isa_dependent_array_type))
            def->stream(os, 0);
    });
}

// class FutharkMemory {
// public:
//     explicit FutharkMemory(World& w)
//         : world_(w) {}

//     void run();

// private:
//     void fill(const Def*);

//     World& world_;
//     DefMap<std::deque<const Def*>> coalesced_intos_;
//     Def2Def result_;
//     DefSet visited_;
// };

// void FutharkMemory::run() {
//     visited_.clear();
//     result_.clear();
//     coalesced_intos_.clear();

//     auto noms = world_.externals() |
//                 std::ranges::views::transform([](auto external) { return external.second->template as_nom<Lam>(); });
//     for (auto nom : noms) {
//         for (auto& op : nom->ops()) fill(op);
//     }
// }

// void FutharkMemory::fill(const Def* def) {
//     if (visited_.contains(def)) return;

//     // if (auto ex = def->isa<Extract>(); ex && !ex->tuple()->arity()->isa<Lit>()) {
//     // } else
//     if (auto in = def->isa<Insert>(); in && !in->tuple()->arity()->isa<Lit>()) {
//         // (a)
//         // check safety cond
//         // src aliases.. do we have those?
//         if (auto it = coalesced_intos_.find(in->tuple()); it != coalesced_intos_.end()) {
//             for (auto src0 : it->second) {
//                 // check safety cond against in.
//             }
//         }
//         // (b)
//         coalesced_intos_[in].push_back(in->tuple());
//         // (c)
//         result_[in->tuple()] = in;
//         if (auto it = coalesced_intos_.find(in->tuple()); it != coalesced_intos_.end()) {
//             for (auto src0 : it->second) { result_[src0] = in; }
//         }
//     } else if (isa_dependent_array(def)) {
//     } else if (isa_dependent_array_type(def->type())) {
//         //     } else if (std::ranges::any_of(def->type()->ops(), isa_dependent_array_type)) {
//         //         node = graph_.insert(def);
//     } else if (auto [app, lam] = isa_apped_nom_lam(def);
//                lam && std::ranges::any_of(lam->dom()->ops(), isa_dependent_array_type)) {
//         for (size_t i = 0, e = app->num_args(); i < e; ++i) {
//             if (auto node = analyze(app->arg(i))) {
//                 if (auto dep = analyze(lam->var(i))) dep->add_child(node);
//             }
//         }
//     }

//     cache_.emplace(def, node);
//     for (const auto* op : def->ops())
//         if (auto dep = analyze(op); dep && node) node->add_child(dep);
// }

void arr2mem(World& w) {
    // ArrAna aana{w};
    // aana.analyze();
    // std::ofstream fana{"arrana.dot"};
    // aana.print(fana);

    // std::ofstream fall{"all.dot"};
    // dot::emit(w, fall);
    // PrintAna ana{w};
    // ana.analyze();

    Arr2Mem a2m{w};
    a2m.run();

    auto direct = Dialect::load("direct", {});
    PassMan man{w};
    auto add_ds2cps =
        reinterpret_cast<decltype(&thorin_add_direct_ds2cps)>(dl::get(direct.handle(), "thorin_add_direct_ds2cps"));
    add_ds2cps(man);
    man.run();
    PassMan::run<LamSpec>(w);
}
} // namespace thorin::mem
