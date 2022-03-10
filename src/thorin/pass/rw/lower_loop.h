#ifndef THORIN_PASS_RW_LOWER_LOOP_H
#define THORIN_PASS_RW_LOWER_LOOP_H

#include "thorin/pass/pass.h"

namespace thorin {


/// Lowers the loop axiom to actual control flow in CPS style
class LowerLoop : public RWPass<Lam> {
public:
    LowerLoop(PassMan& man)
        : RWPass(man, "lower_loop") {}

    const Def* rewrite(const Def*) override;

private:
    Lam2Lam tup2sca_;
};

}

#endif
