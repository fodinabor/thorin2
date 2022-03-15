#include <algorithm>
#include <iterator>
#include <sstream>
#include <stdexcept>

#include <gtest/gtest-param-test.h>
#include <gtest/gtest.h>

#include "thorin/error.h"
#include "thorin/world.h"

#include "thorin/be/ll/ll.h"
#include "thorin/pass/fp/beta_red.h"
#include "thorin/pass/fp/copy_prop.h"
#include "thorin/pass/fp/eta_exp.h"
#include "thorin/pass/fp/eta_red.h"
#include "thorin/pass/pass.h"
#include "thorin/pass/rw/lower_for.h"

using namespace thorin;

class ZipAxiomTest : public testing::TestWithParam<std::tuple<std::vector<int>, std::vector<int>>> {};

TEST(Zip, fold) {
    World w;

    // clang-format off
    auto a = w.tuple({w.tuple({w.lit_int( 0), w.lit_int( 1), w.lit_int( 2)}),
                      w.tuple({w.lit_int( 3), w.lit_int( 4), w.lit_int( 5)})});

    auto b = w.tuple({w.tuple({w.lit_int( 6), w.lit_int( 7), w.lit_int( 8)}),
                      w.tuple({w.lit_int( 9), w.lit_int(10), w.lit_int(11)})});

    auto c = w.tuple({w.tuple({w.lit_int( 6), w.lit_int( 8), w.lit_int(10)}),
                      w.tuple({w.lit_int(12), w.lit_int(14), w.lit_int(16)})});

    auto f = w.fn(Wrap::add, w.lit_nat(0), w.lit_nat(width2mod(32)));
    auto i32_t = w.type_int_width(32);
    auto res = w.app(w.app(w.app(w.ax_zip(), {/*r*/w.lit_nat(2), /*s*/w.tuple({w.lit_nat(2), w.lit_nat(3)})}),
                                             {/*n_i*/ w.lit_nat(2), /*Is*/w.pack(2, i32_t), /*n_o*/w.lit_nat(1), /*Os*/i32_t, f}),
                                             {a, b});
    // clang-format on

    res->dump(0);
    EXPECT_EQ(c, res);
}

TEST_P(ZipAxiomTest, fold) {
    World w;
    auto mem_t  = w.type_mem();
    auto i8_t   = w.type_int_width(8);
    auto i32_t  = w.type_int_width(32);
    auto i64_t  = w.type_int_width(64);
    auto argv_t = w.type_ptr(w.arr(w.top_nat(), w.type_ptr(w.arr(w.top_nat(), i8_t))));

    const auto [A, B] = GetParam();
    EXPECT_EQ(A.size(), B.size());
    std::vector<const Def*> ALits(A.size()), BLits(B.size()), out_lits(A.size());
    std::transform(A.cbegin(), A.cend(), ALits.begin(), [&w, i32_t](int v) { return w.lit_int(i32_t, v); });
    std::transform(B.cbegin(), B.cend(), BLits.begin(), [&w, i32_t](int v) { return w.lit_int(i32_t, v); });
    std::transform(A.cbegin(), A.cend(), B.cbegin(), out_lits.begin(),
                   [&w, i32_t](int a, int b) { return w.lit_int(i32_t, a + b); });

    auto ATup   = w.tuple(ALits);
    auto BTup   = w.tuple(BLits);
    auto OutTup = w.tuple(out_lits);

    auto add = w.fn(Wrap::add, w.lit_nat(0), w.lit_nat(width2mod(32)));
    auto zip = w.app(w.app(w.ax_zip(), {w.lit_nat(1), w.tuple({w.lit_nat(A.size())})}),
                     {w.lit_nat(2), w.pack(2, i32_t), w.lit_nat(1), i32_t, add});
    auto res = w.app(zip, {ATup, BTup});
    EXPECT_EQ(res, OutTup);
}

TEST_P(ZipAxiomTest, zip_dyn) {
    World w;
    auto mem_t  = w.type_mem();
    auto i8_t   = w.type_int_width(8);
    auto i32_t  = w.type_int_width(32);
    auto i64_t  = w.type_int_width(64);
    auto argv_t = w.type_ptr(w.arr(w.top_nat(), w.type_ptr(w.arr(w.top_nat(), i8_t))));

    const auto [A, B] = GetParam();
    EXPECT_EQ(A.size(), B.size());

    std::vector<const Def*> out_lits(A.size());
    std::transform(A.cbegin(), A.cend(), B.cbegin(), out_lits.begin(),
                   [&w, i32_t](int a, int b) { return w.lit_int(i32_t, a + b); });
    auto out_tup = w.tuple(out_lits);

    auto add = w.fn(Wrap::add, w.lit_nat(0), w.lit_nat(width2mod(32)));
    auto zip = w.app(w.app(w.ax_zip(), {w.lit_nat(1), w.tuple({w.lit_nat(A.size())})}),
                     {w.lit_nat(2), w.pack(2, i32_t), w.lit_nat(1), w.tuple({i32_t}), add});

    // Cn [mem, i32, ptr(ptr(i32, 0), 0) Cn [mem, i32]]
    auto main_t = w.cn({mem_t, i32_t, argv_t, w.cn({mem_t, i32_t})});
    auto main   = w.nom_lam(main_t, w.dbg("main"));

    auto parse_arrays_ret_t = w.cn({mem_t, w.type_ptr(w.arr(w.lit_nat(2), w.type_ptr(w.arr(w.top_nat(), i32_t))))});
    // int **parseArrays(int argc, const char* argv[], int &arrlength)
    // Cn [:mem, :i32, :ptr («⊤∷nat; i8», 0∷nat), :ptr(i32, 0∷nat), Cn [:mem, :ptr(«2∷nat; :ptr(«T∷nat; i32»)»)])]
    auto parse_arrays_t = w.cn({mem_t, i32_t, argv_t, w.type_ptr(i32_t), parse_arrays_ret_t});

    auto parse_arrays     = w.nom_lam(parse_arrays_t, w.dbg("parse_arrays"));
    auto parse_arrays_ret = w.nom_lam(parse_arrays_ret_t, w.dbg("parse_arrays_cont"));

    auto [arr_len_slot_mem, arr_len_slot] = w.op_slot(i32_t, main->mem_var(), w.dbg("array_length"))->projs<2>();
    {
        auto [mem, ptr]      = parse_arrays_ret->vars<2>();
        auto [a_mem, ab_ptr] = w.op_load(mem, ptr)->projs<2>();
        auto [a_ptr, b_ptr]  = ab_ptr->projs<2>();
        // auto [b_mem, b_ptr]     = w.op_load(a_mem, w.op_lea(ptr, w.lit_int_width(1, 1)))->projs<2>();
        auto [len_mem, arr_len] = w.op_load(a_mem, arr_len_slot)->projs<2>();

        auto a_t              = w.arr(w.top_nat(), i32_t);
        auto a                = w.lit(a_t, 0);
        auto b_t              = w.arr(w.top_nat(), i32_t);
        auto b                = w.lit(b_t, 0);
        auto accumulator_type = w.sigma({a_ptr->type(), b_ptr->type(), a_t, b_t});

        auto yield_type = w.cn({mem_t, accumulator_type});
        auto load_arrs  = w.nom_lam(w.cn({mem_t, i32_t, accumulator_type, yield_type}), w.dbg("load_arrays"));
        {
            auto [mem, iter, accumulators, yield] =
                load_arrs->vars<4>({w.dbg("mem"), w.dbg("iter"), w.dbg("accumulators"), w.dbg("yield")});
            auto [a_ptr, b_ptr, a, b] = accumulators->projs<4>();

            auto [a_mem, a_val] = w.op_load(mem, w.op_lea(a_ptr, iter))->projs<2>();
            auto [b_mem, b_val] = w.op_load(a_mem, w.op_lea(b_ptr, iter))->projs<2>();
            auto a_inserted     = w.insert(a, iter, a_val);
            auto b_inserted     = w.insert(b, iter, b_val);
            load_arrs->app(false, yield, {b_mem, w.tuple({a_ptr, b_ptr, a_inserted, b_inserted})});
        }

        auto load_arrs_cont = w.nom_lam(w.cn({mem_t, accumulator_type}), w.dbg("load_arrays_cont"));

        parse_arrays_ret->set_filter(false);
        parse_arrays_ret->set_body(w.op_for({a_ptr->type(), b_ptr->type(), a->type(), b->type()}, len_mem,
                                            w.lit_int_width(32, 0), arr_len, w.lit_int_width(32, 1),
                                            {a_ptr, b_ptr, a, b}, load_arrs, load_arrs_cont));

        {
            auto [mem, ab_tpl]        = load_arrs_cont->vars<2>();
            auto [a_ptr, b_ptr, a, b] = ab_tpl->projs<4>();
            auto zip_res              = w.app(zip, {a, b});
            zip->dump(0);
            zip->dump(5);
            zip_res->dump(0);
            zip_res->dump(5);
            // auto zip_res       = out_tup;

            { // compare
                auto accumulator_type = w.sigma({i32_t, zip_res->type(), out_tup->type()});
                auto yield_type       = w.cn({mem_t, accumulator_type});
                auto body_type        = w.cn({mem_t, i32_t, accumulator_type, yield_type});

                auto body = w.nom_lam(body_type, w.dbg("compare_body"));
                {
                    auto [mem, i, acc_tpl, yield] =
                        body->vars<4>({w.dbg("mem"), w.dbg("i"), w.dbg("acc_tpl"), w.dbg("yield")});

                    auto [errors, zip_res, gt] = acc_tpl->projs<3>({w.dbg("errors"), w.dbg("zip_res"), w.dbg("gt")});

                    auto idx = w.op(Conv::u2u, w.type_int(out_tup->arity()), i);
                    auto add = w.op(Wrap::add, w.lit_nat(0), errors,
                                    w.select(w.lit_int(errors->type(), 0), w.lit_int(errors->type(), 1),
                                             w.op(ICmp::e, w.extract(zip_res, idx), w.extract(gt, idx))));
                    body->app(false, yield, {mem, w.tuple({add, zip_res, gt})});
                }

                auto ret_cont = w.nom_lam(w.cn({mem_t, accumulator_type}), w.dbg("ret_cont"));
                {
                    auto [mem, acc_tpl]        = ret_cont->vars<2>();
                    auto [errors, zip_res, gt] = acc_tpl->projs<3>();
                    ret_cont->app(false, main->ret_var(), {mem, errors});
                }

                load_arrs_cont->set_filter(false);
                load_arrs_cont->set_body(w.op_for({i32_t, zip_res->type(), out_tup->type()}, mem,
                                                  w.lit_int_width(32, 0), arr_len, w.lit_int_width(32, 1),
                                                  {w.lit_int_width(32, 0), zip_res, out_tup}, body, ret_cont));
            }
        }
    }
    {
        auto [mem, argc, argv, ret] = main->vars<4>();
        main->app(false, parse_arrays, {arr_len_slot_mem, argc, argv, arr_len_slot, parse_arrays_ret});
    }

    main->make_external();
    main->dump(20);

    Stream cs{};
    w.stream(cs);

    PassMan man{w};
    man.add<LowerFor>();
    man.run();

    PassMan opt{w};
    auto br = opt.add<BetaRed>();
    auto er = opt.add<EtaRed>();
    auto ee = opt.add<EtaExp>(er);
    opt.add<CopyProp>(br, ee);
    opt.run();

    w.stream(cs);

    std::ofstream file("test.ll");
    Stream s(file);
    ll::emit(w, s);
    file.close();

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
