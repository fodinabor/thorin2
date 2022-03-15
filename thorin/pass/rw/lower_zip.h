#ifndef THORIN_PASS_RW_LOWER_ZIP_H
#define THORIN_PASS_RW_LOWER_ZIP_H

#include "thorin/pass/pass.h"

namespace thorin {

/// Lowers the zip axiom to use the affine for axiom.
/// Requires CopyProp to cleanup afterwards.
/// Should run in a dedicated lowering phase.
class LowerZip : public RWPass<Lam> {
public:
    LowerZip(PassMan& man)
        : RWPass(man, "lower_zip") {}

    const Def* rewrite(const Def*) override;
};

} // namespace thorin

#endif
