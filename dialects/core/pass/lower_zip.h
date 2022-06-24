#ifndef THORIN_PASS_RW_LOWER_ZIP_H
#define THORIN_PASS_RW_LOWER_ZIP_H

#include "thorin/def.h"

#include "thorin/pass/pass.h"

namespace thorin::core {

/// Lowers the zip axiom to use the affine for axiom.
/// Requires CopyProp to cleanup afterwards.
/// Should run in a dedicated lowering phase.
class LowerZip : public RWPass<Lam> {
public:
    LowerZip(PassMan& man)
        : RWPass(man, "lower_zip") {}

    void enter() override { found_zip_.reset(); }

    const Def* rewrite(const Def*) override;

    static PassTag* ID();

private:
    Def2Def rewritten_;
    std::optional<const Def*> found_zip_;
};

} // namespace thorin::core

#endif
