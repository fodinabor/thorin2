#include "thorin/pass/rw/lower_loop.h"
#include "thorin/tables.h"

namespace thorin {

const Def* LowerLoop::rewrite(const Def *def) {
    if(auto app = def->isa<App>())
        if(auto loop = app->axiom(); loop && loop->tag() == Tag::Loop) {
            app->dump(5);
            auto args = app->op(1);
            args->dump(5);
        }
            
    return def;
}

}