#include "dialects/core/pass/lower_zip.h"

#include "thorin/def.h"
#include "thorin/tables.h"

#include "thorin/util/array.h"

#include "dialects/affine/affine.h"
#include "dialects/core/core.h"
#include "dialects/mem/mem.h"

namespace thorin::core {

const Def* LowerZip::rewrite(const Def* def) {
    if (auto cached = rewritten_.find(def); cached != rewritten_.end()) return cached->second;
    if (auto zip = match<core::zip>(def)) {
        found_zip_ = zip;
        return def;
    }
    if (found_zip_.has_value() && def == curr_nom()->body()) {
        auto zip = found_zip_.value()->as<App>();
        auto& w  = world();
        w.DLOG("rewriting zip axiom: {} within {}", zip, curr_nom());

        auto app2 = zip->callee()->as<App>();
        // auto app1 = app2->callee()->as<App>();

        auto [zip_in1, zip_in2]                             = zip->args<2>();
        auto [in_shape, in_type, out_shape, out_type, func] = app2->args<5>();

        auto arr_len = zip->type()->as<Arr>()->shape(); // todo: multi dim shapes

        auto accumulator_type = w.sigma({zip_in1->type(), zip_in2->type(), zip->type()});
        auto yield_type       = w.cn({mem::type_mem(w), accumulator_type});
        auto iter_type        = w.type_int(arr_len);
        auto for_body = w.nom_lam(w.cn({mem::type_mem(w), iter_type, accumulator_type, yield_type}), w.dbg("zip_body"));
        { // construct body
            auto [mem, iter, acc_tpl, yield] =
                for_body->vars<4>({w.dbg("mem"), w.dbg("iter"), w.dbg("accumulators"), w.dbg("yield")});
            auto [in1, in2, out] = acc_tpl->projs<3>({zip_in1->dbg(), zip_in2->dbg(), w.dbg("out")});

            auto new_out = w.insert(out, iter, w.app(func, {w.extract(in1, iter), w.extract(in2, iter)}));
            for_body->app(false, yield, {mem, w.tuple({in1, in2, new_out})});
        }

        auto for_cont = w.nom_lam(w.cn({mem::type_mem(w), accumulator_type}), w.dbg("zip_cont"));
        { // construct break
            auto [mem, acc_tpl] = for_cont->vars<2>();
            auto out            = acc_tpl->proj(2);
            std::vector<const Def*> wl;
            Def2Def local_map;
            // todo: what if the memvar is used in an op zip depends on?
            auto mem_var       = mem::mem_var(curr_nom());
            local_map[mem_var] = mem;
            wl.insert(wl.end(), mem_var->uses().begin(), mem_var->uses().end());
            local_map[zip] = out;
            wl.insert(wl.end(), zip->uses().begin(), zip->uses().end());
            while (!wl.empty()) {
                auto back = wl.back();
                back->dump(0);
                wl.pop_back();
                if (auto nom = back->isa_nom()) {
                    if (nom == curr_nom()) continue;
                    for (size_t i = 0; i < nom->num_ops(); ++i)
                        if (auto cached = local_map.find(nom->op(i)); cached != local_map.end())
                            nom->set(i, cached->second);
                    continue;
                }

                wl.insert(wl.end(), back->uses().begin(), back->uses().end());
                DefArray new_ops{back->num_ops(), [&](size_t i) {
                                     auto op = back->op(i);
                                     if (auto cached = local_map.find(op); cached != local_map.end())
                                         return cached->second;
                                     return op;
                                 }};
                local_map[back] = back->rebuild(w, back->type(), new_ops, back->dbg());
            }

            for_cont->set_filter(false);
            for_cont->set_body(local_map[curr_nom()->body()]);
            rewritten_[zip] = out;
        }
        // todo: memvar?!
        auto new_body = affine::op_for(mem::mem_var(curr_nom()), w.lit_int(iter_type, 0_s),
                                       w.op_bitcast(iter_type, arr_len), w.lit_int(iter_type, 1),
                                       {zip_in1, zip_in2, w.pack(arr_len, w.lit(out_type, 0_s))}, for_body, for_cont);
        w.dump();
        return rewritten_[def] = new_body;
    }

    return def;
}

PassTag* LowerZip::ID() {
    static PassTag Key;
    return &Key;
}

} // namespace thorin::core