#ifndef THORIN_PASS_RW_ARR2MEM_H
#define THORIN_PASS_RW_ARR2MEM_H

#include "thorin/config.h"
#include "thorin/def.h"

namespace thorin {
class Lam;
namespace mem {

class Arr2MemAnalysis {
    virtual void analyze() {}
    virtual const Def* coalesced_into(const Def*) const { return nullptr; }
};

// Lower dependently sized arrays to memory.
class Arr2Mem {
public:
    Arr2Mem(World& world)
        : world_(world) {}

    void run();
    const Def* rewrite(Lam* nom);
    const Def* rewrite(Lam*& curr_nom, const Def*);

    const Def* replace_proxy_with_var(Lam*, const Def*);

private:
    World& world_;
    Def2Def rewritten_;
    Def2Def val2mem_;
    std::vector<Lam*> noms_;
    Def2Def proxy_rewritten_;
};

void arr2mem(World&);

} // namespace mem
} // namespace thorin

#endif
