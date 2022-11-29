#include "dialects/core/pass/rw/lower_zip.h"

#include "thorin/def.h"
#include "thorin/lam.h"
#include "thorin/rewrite.h"

#include "thorin/analyses/scope.h"
#include "thorin/util/array.h"

#include "dialects/affine/affine.h"
#include "dialects/core/core.h"
#include "dialects/direct/direct.h"
#include "dialects/mem/mem.h"

namespace thorin::core {

const Def* LowerZip::rewrite(const Def* def) {
    if (auto cached = rewritten_.find(def); cached != rewritten_.end()) return cached->second;
    if (auto zip = match<core::zip>(def)) {
        auto& w = world();
        w.DLOG("rewriting zip axiom: {} within {}", zip, curr_nom());

        auto app2 = zip->callee()->as<App>();

        auto [zip_in1, zip_in2]                             = zip->args<2>();
        auto [in_shape, in_type, out_shape, out_type, func] = app2->args<5>();

        auto arr_len = zip->type()->as<Arr>()->shape(); // todo: multi dim shapes

        auto accumulator_type = w.sigma({zip->type()});
        auto yield_type       = w.cn(accumulator_type);
        auto iter_type        = w.type_idx(0_s);
        auto for_body         = w.nom_lam(w.cn({iter_type, accumulator_type, yield_type}), w.dbg("zip_body"));
        { // construct body
            auto [iter, acc_tpl, yield] = for_body->vars<3>({w.dbg("iter"), w.dbg("accumulators"), w.dbg("yield")});
            auto out                    = acc_tpl;

            auto idx     = core::op(core::conv::u2u, w.type_idx(arr_len), iter);
            auto new_out = w.insert(out, idx, w.app(func, {w.extract(zip_in1, idx), w.extract(zip_in2, idx)}));
            for_body->app(false, yield, new_out);
        }

        DefArray acc_args{w.pack(arr_len, w.lit(out_type, 0_s))};
        DefArray acc_types(acc_args, [](auto&& op) { return op->type(); });
        auto fn_for      = affine::fn_for(world(), iter_type, acc_types);
        auto callee_type = fn_for->type()->as<Pi>();
        auto wrapper = w.nom_lam(w.cn({w.sigma(callee_type->doms().skip_back()), callee_type->doms().back()}), nullptr);
        DefArray args{callee_type->num_doms(), [&](size_t i) {
                          if (i < callee_type->num_doms() - 1) return wrapper->var(0_s)->proj(i);
                          return wrapper->var(1);
                      }};
        wrapper->app(false, fn_for, args);
        auto new_zip =
            w.app(direct::op_cps2ds_dep(wrapper), w.tuple({w.lit(iter_type, 0_s), core::op_bitcast(iter_type, arr_len),
                                                           w.lit(iter_type, 1), w.tuple(acc_args), for_body}));
        return rewritten_[zip] = new_zip;
    }

    return def;
}

PassTag* LowerZip::ID() {
    static PassTag Key;
    return &Key;
}

} // namespace thorin::core