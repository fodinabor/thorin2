#pragma once

#include "thorin/def.h"

#include "thorin/pass/pass.h"

namespace thorin::core {

/// Lowers the zip axiom to use the affine for axiom.
/// Requires LowerFor and DS2CPS to remove newly introduced axioms afterwards.
class LowerZip : public RWPass<LowerZip, Lam> {
public:
    LowerZip(PassMan& man)
        : RWPass(man, "lower_zip") {}

    const Def* rewrite(const Def*) override;

    static PassTag* ID();

private:
    Def2Def rewritten_;
};

} // namespace thorin::core
