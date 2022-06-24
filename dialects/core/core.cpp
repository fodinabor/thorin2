#include "dialects/core.h"

#include <thorin/config.h>
#include <thorin/pass/pass.h>

#include "thorin/dialects.h"

#include "thorin/pass/pipelinebuilder.h"

#include "dialects/core/be/ll/ll.h"
#include "dialects/core/pass/lower_zip.h"

using namespace thorin;

extern "C" THORIN_EXPORT DialectInfo thorin_get_dialect_info() {
    return {"core",
            [](PipelineBuilder& builder) { builder.extend_opt_phase([](PassMan& man) { man.add<core::LowerZip>(); }); },
            [](Backends& backends) { backends["ll"] = &ll::emit; },
            [](Normalizers& normalizers) { core::register_normalizers(normalizers); }};
}
