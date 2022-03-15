#include "thorin/pass/rw/lower_zip.h"

using namespace thorin;

const Def* LowerZip::rewrite(const Def* def) {
    if (auto zip = isa<Tag::Zip>(def)) { def->dump(5); }

    return def;
}