#pragma once

#include "thorin/world.h"

#include "dialects/direct/autogen.h"

namespace thorin::direct {
// .ax %direct.ds2cps: Π [T: *, U: *] -> (T -> U) -> .Cn [T, .Cn U];
inline const Def* op_ds2cps(const Def* ds_fun) {
    auto& w   = ds_fun->world();
    auto type = ds_fun->type()->as<Pi>();
    return w.app(w.app(w.ax<direct::ds2cps>(), {type->dom(), type->codom()}), ds_fun);
}

// .ax %direct.cps2ds: Π [T: *, U: *] -> (.Cn [T, .Cn U]) -> (T -> U);
inline const Def* op_cps2ds(const Def* cps_fun) {
    auto& w   = cps_fun->world();
    auto type = cps_fun->type()->as<Pi>();
    assert(type->num_doms() == 2 && "function wrapped by cps2ds must have exactly 2 arguments (args, cn)");
    return w.app(w.app(w.ax<direct::cps2ds>(), {type->dom(0), type->dom(1)->as<Pi>()->dom()}), cps_fun);
}

} // namespace thorin::direct

extern "C" THORIN_EXPORT thorin::IPass* thorin_add_direct_ds2cps(thorin::PassMan&);
