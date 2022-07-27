#pragma once

#include "thorin/world.h"

#include "dialects/direct/autogen.h"

namespace thorin::direct {} // namespace thorin::direct

extern "C" THORIN_EXPORT thorin::IPass* thorin_add_direct_ds2cps(thorin::PassMan&);
