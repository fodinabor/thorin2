#pragma once

#include <queue>

#include "thorin/phase/phase.h"

namespace thorin::mem {

using DefQueue = std::deque<const Def*>;

static int i = 0;
class Reshape : public RWPass<Reshape, Lam> {
public:
    enum Mode{
        Flat, Arg
    };

    Reshape(PassMan& man, Mode mode)
        : RWPass(man, "reshape"),
            mode_(mode) {}

    void enter() override;

private:
    /// Recursively rewrites a Def.
    const Def* rewrite(const Def* def);
    const Def* rewrite_convert(const Def* def);

    const Def* convert(const Def* def);
    const Def* convert_ty(const Def* ty);
    const Def* flatten_ty(const Def* ty);
    const Def* flatten_ty_convert(const Def* ty);
    void aggregate_sigma(const Def* ty, DefQueue& ops);
    const Def* wrap(const Def* def, const Def* target_ty);
    const Def* reshape(const Def* mem, const Def* ty, DefQueue& vars);
    const Def* reshape(const Def* arg, const Pi* target_pi);
    //const Def* make_scalar_inv(const Def* def, const Def* ty);

    Def2Def old2new_;
    std::stack<Lam*> worklist_;
    Mode mode_;
    Def2Def old2flatten_;
};

} // namespace thorin::clos
