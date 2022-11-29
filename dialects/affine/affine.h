#pragma once

#include "thorin/axiom.h"
#include "thorin/world.h"

#include "dialects/affine/autogen.h"

namespace thorin::affine {

/// Returns the affine_for axiom applied with \a params.
/// See documentation for %affine.For axiom in @ref affine.
inline const Def* fn_for(World& w, const Def* iter_type, Defs params) {
    assert(iter_type->isa<Idx>() && "affine.for expects Int as iter type");
    return w.app(w.ax<affine::For>(), {iter_type->as<App>()->arg(), w.lit_nat(params.size()), w.tuple(params)});
}

/// Returns a fully applied affine_for axiom.
/// See documentation for %affine.For axiom in @ref affine.
inline const Def*
op_for(const Def* begin, const Def* end, const Def* step, Defs inits, const Def* body, const Def* brk) {
    World& w = begin->world();
    DefArray types(inits.size(), [&](size_t i) { return inits[i]->type(); });
    return w.app(fn_for(w, begin->type(), types), {begin, end, step, w.tuple(inits), body, brk});
}
} // namespace thorin::affine
