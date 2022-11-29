#include <algorithm>
#include <fstream>
#include <iterator>
#include <sstream>
#include <stdexcept>

#include <gtest/gtest-param-test.h>
#include <gtest/gtest.h>

#include "thorin/dialects.h"
#include "thorin/error.h"
#include "thorin/world.h"

#include "thorin/fe/parser.h"
#include "thorin/pass/optimize.h"
#include "thorin/pass/pass.h"

#include "dialects/affine/affine.h"
#include "dialects/core/autogen.h"
#include "dialects/core/core.h"
#include "dialects/core/pass/rw/lower_zip.h"
#include "dialects/mem/mem.h"

using namespace thorin;

class ZipAxiomTest : public testing::TestWithParam<std::tuple<std::vector<int>, std::vector<int>>> {};

TEST(Zip, fold) {
    World w;

    Normalizers normalizers;
    auto core_d = Dialect::load("core", {});
    core_d.register_normalizers(normalizers);
    fe::Parser::import_module(w, "core", {}, &normalizers);

    // clang-format off
    auto a = w.tuple({w.tuple({w.lit_idx( 0), w.lit_idx( 1), w.lit_idx( 2)}),
                      w.tuple({w.lit_idx( 3), w.lit_idx( 4), w.lit_idx( 5)})});

    auto b = w.tuple({w.tuple({w.lit_idx( 6), w.lit_idx( 7), w.lit_idx( 8)}),
                      w.tuple({w.lit_idx( 9), w.lit_idx(10), w.lit_idx(11)})});

    auto c = w.tuple({w.tuple({w.lit_idx( 6), w.lit_idx( 8), w.lit_idx(10)}),
                      w.tuple({w.lit_idx(12), w.lit_idx(14), w.lit_idx(16)})});

    auto f = core::fn(core::wrap::add, w.lit_nat(Idx::bitwidth2size(32)), 0_n);
    auto i32_t = w.type_int(32);
    auto res = w.app(w.app(w.app(w.ax<core::zip>(), {/*r*/w.lit_nat(2), /*s*/w.tuple({w.lit_nat(2), w.lit_nat(3)})}),
                                             {/*n_i*/ w.lit_nat(2), /*Is*/w.pack(2, i32_t), /*n_o*/w.lit_nat(1), /*Os*/i32_t, f}),
                                             {a, b});
    // clang-format on

    res->dump(0);
    EXPECT_EQ(c, res);
}

TEST_P(ZipAxiomTest, fold) {
    World w;

    Normalizers normalizers;
    auto mem_d = Dialect::load("mem", {});
    mem_d.register_normalizers(normalizers);
    fe::Parser::import_module(w, "mem", {}, &normalizers);

    auto core_d = Dialect::load("core", {});
    core_d.register_normalizers(normalizers);
    fe::Parser::import_module(w, "core", {}, &normalizers);

    auto i32_t = w.type_int(32);

    const auto [A, B] = GetParam();
    EXPECT_EQ(A.size(), B.size());
    std::vector<const Def*> ALits(A.size()), BLits(B.size()), out_lits(A.size());
    std::transform(A.cbegin(), A.cend(), ALits.begin(), [&w, i32_t](int v) { return w.lit(i32_t, v); });
    std::transform(B.cbegin(), B.cend(), BLits.begin(), [&w, i32_t](int v) { return w.lit(i32_t, v); });
    std::transform(A.cbegin(), A.cend(), B.cbegin(), out_lits.begin(),
                   [&w, i32_t](int a, int b) { return w.lit(i32_t, a + b); });

    auto ATup   = w.tuple(ALits);
    auto BTup   = w.tuple(BLits);
    auto OutTup = w.tuple(out_lits);

    auto add = core::fn(core::wrap::add, w.lit_nat(0), w.lit_nat(Idx::bitwidth2size(32)));
    auto zip = w.app(w.app(w.ax<core::zip>(), {w.lit_nat(1), w.tuple({w.lit_nat(A.size())})}),
                     {w.lit_nat(2), w.pack(2, i32_t), w.lit_nat(1), i32_t, add});
    auto res = w.app(zip, {ATup, BTup});
    EXPECT_EQ(res, OutTup);
}

TEST_P(ZipAxiomTest, zip_dyn) {
    World w;

    Normalizers normalizers;
    auto mem_d = Dialect::load("mem", {});
    mem_d.register_normalizers(normalizers);
    fe::Parser::import_module(w, mem_d.name(), {}, &normalizers);

    auto core_d = Dialect::load("core", {});
    core_d.register_normalizers(normalizers);
    fe::Parser::import_module(w, core_d.name(), {}, &normalizers);

    auto affine_d = Dialect::load("affine", {});
    affine_d.register_normalizers(normalizers);
    fe::Parser::import_module(w, affine_d.name(), {}, &normalizers);

    auto direct_d = Dialect::load("direct", {});
    direct_d.register_normalizers(normalizers);
    fe::Parser::import_module(w, direct_d.name(), {}, &normalizers);

    auto mem_t  = mem::type_mem(w);
    auto i8_t   = w.type_int(8);
    auto i32_t  = w.type_int(32);
    auto i64_t  = w.type_int(64);
    auto argv_t = mem::type_ptr(w.arr(w.top_nat(), mem::type_ptr(w.arr(w.top_nat(), i8_t))));

    const auto [A, B] = GetParam();
    EXPECT_EQ(A.size(), B.size());

    std::vector<const Def*> out_lits(A.size());
    std::transform(A.cbegin(), A.cend(), B.cbegin(), out_lits.begin(),
                   [&w, i32_t](int a, int b) { return w.lit(i32_t, a + b); });
    auto out_tup = w.tuple(out_lits);

    auto add = core::fn(core::wrap::add, w.lit_nat(0), w.lit_nat(Idx::bitwidth2size(32)));

    // Cn [mem, i32, ptr(ptr(i32, 0), 0) Cn [mem, i32]]
    auto main_t = w.cn({mem_t, i32_t, argv_t, w.cn({mem_t, i32_t})});
    auto main   = w.nom_lam(main_t, w.dbg("main"));

    auto parse_arrays_ret_t =
        w.cn({mem_t, mem::type_ptr(w.arr(w.lit_nat(2), mem::type_ptr(w.arr(w.top_nat(), i32_t))))});
    // int **parseArrays(int argc, const char* argv[], int &arrlength)
    // Cn [:mem, :i32, :ptr («⊤∷nat; i8», 0∷nat), :ptr(i32, 0∷nat), Cn [:mem, :ptr(«2∷nat; :ptr(«T∷nat; i32»)»)])]
    auto parse_arrays_t = w.cn({mem_t, i32_t, argv_t, mem::type_ptr(i32_t), parse_arrays_ret_t});

    auto parse_arrays     = w.nom_lam(parse_arrays_t, w.dbg("parse_arrays"));
    auto parse_arrays_ret = w.nom_lam(parse_arrays_ret_t, w.dbg("parse_arrays_cont"));

    auto [arr_len_slot_mem, arr_len_slot] =
        mem::op_mslot(i32_t, mem::mem_var(main), w.lit_nat(w.curr_gid()), w.dbg("array_length"))->projs<2>();
    {
        auto [mem, ptr]      = parse_arrays_ret->vars<2>();
        auto [a_mem, ab_ptr] = mem::op_load(mem, ptr)->projs<2>();
        auto [a_ptr, b_ptr]  = ab_ptr->projs<2>();
        // auto [b_mem, b_ptr]     = w.op_load(a_mem, w.op_lea(ptr, w.lit_int_width(1, 1)))->projs<2>();
        auto [len_mem, arr_len] = mem::op_load(a_mem, arr_len_slot)->projs<2>();
        auto nat_arr_len        = core::op_bitcast(w.type_nat(), core::op(core::conv::u2u, i64_t, arr_len));
        auto a                  = w.pack(nat_arr_len, w.lit(i32_t, 0_u32));
        auto b                  = w.pack(nat_arr_len, w.lit(i32_t, 0_u32));
        auto accumulator_type   = w.sigma({mem::type_mem(w), a_ptr->type(), b_ptr->type(), a->type(), b->type()});

        auto yield_type = w.cn(accumulator_type);
        auto load_arrs  = w.nom_lam(w.cn({i32_t, accumulator_type, yield_type}), w.dbg("load_arrays"));
        {
            auto [iter, accumulators, yield] =
                load_arrs->vars<3>({w.dbg("iter"), w.dbg("accumulators"), w.dbg("yield")});
            auto [mem, a_ptr, b_ptr, a, b] = accumulators->projs<5>();

            auto [a_mem, a_val] = mem::op_load(mem, mem::op_lea(a_ptr, iter))->projs<2>();
            auto [b_mem, b_val] = mem::op_load(a_mem, mem::op_lea(b_ptr, iter))->projs<2>();
            auto index          = core::op(core::conv::u2u, w.type_idx(a->arity()), iter);
            auto a_inserted     = w.insert(a, index, a_val);
            auto b_inserted     = w.insert(b, index, b_val);
            load_arrs->app(false, yield, w.tuple({b_mem, a_ptr, b_ptr, a_inserted, b_inserted}));
        }

        auto load_arrs_cont = w.nom_lam(w.cn(accumulator_type), w.dbg("load_arrays_cont"));

        parse_arrays_ret->set_filter(false);
        parse_arrays_ret->set_body(affine::op_for(w.lit_int(32, 0), arr_len, w.lit_int(32, 1),
                                                  {len_mem, a_ptr, b_ptr, a, b}, load_arrs, load_arrs_cont));

        {
            auto ab_tpl                    = load_arrs_cont->var();
            auto [mem, a_ptr, b_ptr, a, b] = ab_tpl->projs<5>();
            auto zip                       = w.app(w.app(w.ax<core::zip>(), {w.lit_nat(1), w.tuple({a->arity()})}),
                                                   {w.lit_nat(2), w.pack(2, i32_t), w.lit_nat(1), w.tuple({i32_t}), add});
            auto zip_res                   = w.app(zip, {a, b});
            zip->dump(0);
            zip->dump(5);
            zip_res->dump(0);
            zip_res->dump(5);
            // auto zip_res       = out_tup;

            { // compare
                auto accumulator_type = w.sigma({i32_t, zip_res->type(), out_tup->type()});
                auto yield_type       = w.cn(accumulator_type);
                auto body_type        = w.cn({i32_t, accumulator_type, yield_type});

                auto body = w.nom_lam(body_type, w.dbg("compare_body"));
                {
                    auto [i, acc_tpl, yield] = body->vars<3>({w.dbg("i"), w.dbg("acc_tpl"), w.dbg("yield")});

                    auto [errors, zip_res, gt] = acc_tpl->projs<3>({w.dbg("errors"), w.dbg("zip_res"), w.dbg("gt")});

                    auto add = core::op(
                        core::wrap::add, w.lit_nat(0), errors,
                        w.select(w.lit(errors->type(), 0), w.lit(errors->type(), 1),
                                 core::op(core::icmp::e, w.extract(zip_res, core::op(core::conv::u2u, w.type_idx(zip_res->arity()), i)),
                                      w.extract(gt, core::op(core::conv::u2u, w.type_idx(gt->arity()), i)))));
                    body->app(false, yield, w.tuple({add, zip_res, gt}));
                }

                auto ret_cont = w.nom_lam(w.cn(accumulator_type), w.dbg("ret_cont"));
                {
                    auto acc_tpl               = ret_cont->var();
                    auto [errors, zip_res, gt] = acc_tpl->projs<3>();
                    ret_cont->app(false, main->ret_var(), {mem, errors});
                }

                load_arrs_cont->set_filter(false);
                load_arrs_cont->set_body(affine::op_for(w.lit_int(32, 0), arr_len, w.lit_int(32, 1),
                                                        {w.lit_int(32, 0), zip_res, out_tup}, body, ret_cont));
            }
        }
    }
    {
        auto [mem, argc, argv, ret] = main->vars<4>();
        main->app(false, parse_arrays, {arr_len_slot_mem, argc, argv, arr_len_slot, parse_arrays_ret});
    }

    main->make_external();
    main->dump(20);

    w.dump();

    PipelineBuilder builder;
    mem_d.register_passes(builder);
    affine_d.register_passes(builder);
    core_d.register_passes(builder);
    direct_d.register_passes(builder);
    optimize(w, builder);

    w.dump();

    Backends backends;
    core_d.register_backends(backends);

    {
        std::ofstream file("test.ll");
        backends["ll"](w, file);
    }

    // TODO make sure that proper clang is in path on Windows
#ifndef _MSC_VER
    std::stringstream cmdStream;
    cmdStream << "./test ";
    for (size_t i = 0; i < A.size(); ++i) { cmdStream << A[i] << " "; }
    for (size_t i = 0; i < B.size(); ++i) { cmdStream << B[i] << " "; }

    EXPECT_EQ(0, WEXITSTATUS(std::system("clang test.ll -o `pwd`/test -Wno-override-module")));
    EXPECT_EQ(0, WEXITSTATUS(std::system(cmdStream.str().c_str())));
#endif
}

// test with these begin, end, step combinations:
INSTANTIATE_TEST_SUITE_P(Axiom,
                         ZipAxiomTest,
                         testing::Values(
                             std::tuple{
                                 std::vector<int>{1, 2, 3, 4,  5},
                                 std::vector<int>{6, 7, 8, 9, 10}
},
                             std::tuple{std::vector<int>{1, 2, 3, 4, 5, 11, 12, 13, 14, 15},
                                        std::vector<int>{6, 7, 8, 9, 10, 16, 17, 18, 19, 20}}));
