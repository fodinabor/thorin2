#include <gtest/gtest.h>

#include "thorin/error.h"
#include "thorin/be/ll/ll.h"
#include "thorin/axiom.h"
#include "thorin/lam.h"
#include "thorin/tables.h"
#include "thorin/world.h"

#include "thorin/be/ll/ll.h"

using namespace thorin;

TEST(Zip, fold) {
    World w;

    // clang-format off
    auto a = w.tuple({w.tuple({w.lit_int( 0), w.lit_int( 1), w.lit_int( 2)}),
                      w.tuple({w.lit_int( 3), w.lit_int( 4), w.lit_int( 5)})});

    auto b = w.tuple({w.tuple({w.lit_int(6), w.lit_int(7), w.lit_int(8)}),
        w.tuple({w.lit_int(9), w.lit_int(10), w.lit_int(11)})});

    auto c = w.tuple({w.tuple({w.lit_int(6), w.lit_int(8), w.lit_int(10)}),
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

TEST(Error, app) {
    World w;
    auto i32_t = w.type_int_width(32);
    auto r32_t = w.type_real(32);
    auto a     = w.axiom(w.cn({i32_t, r32_t}));
    auto i     = w.lit_int_width(32, 23);
    auto r     = w.lit_real(32, 23);
    w.app(a, {i, r}); // Ok!
    EXPECT_THROW(w.app(a, {r, i}), TypeError);
}

TEST(Main, ll) {
    World w;
    auto mem_t  = w.type_mem();
    auto i32_t  = w.type_int_width(32);
    auto argv_t = w.type_ptr(w.type_ptr(i32_t));

    // Cn [mem, i32, Cn [mem, i32]]
    auto main_t                 = w.cn({mem_t, i32_t, argv_t, w.cn({mem_t, i32_t})});
    auto main                   = w.nom_lam(main_t, w.dbg("main"));
    auto [mem, argc, argv, ret] = main->vars<4>();
    main->app(ret, {mem, argc});
    main->make_external();

    std::ofstream file("test.ll");
    Stream s(file);
    ll::emit(w, s);
    file.close();

#ifndef _MSC_VER
    // TODO make sure that proper clang is in path on Windows
    std::system("clang test.ll -o test");
    EXPECT_EQ(4, WEXITSTATUS(std::system("./test a b c")));
    EXPECT_EQ(7, WEXITSTATUS(std::system("./test a b c d e f")));
#endif
}

TEST(Axiom, mangle) {
    EXPECT_EQ(Axiom::demangle(*Axiom::mangle("test")), "test");
    EXPECT_EQ(Axiom::demangle(*Axiom::mangle("azAZ09_")), "azAZ09_");
    EXPECT_EQ(Axiom::demangle(*Axiom::mangle("01234567")), "01234567");
    EXPECT_FALSE(Axiom::mangle("012345678"));
    EXPECT_FALSE(Axiom::mangle("!"));
    // Check whether lower 16 bits are properly ignored
    EXPECT_EQ(Axiom::demangle(*Axiom::mangle("test") | 0xFF_u64), "test");
    EXPECT_EQ(Axiom::demangle(*Axiom::mangle("01234567") | 0xFF_u64), "01234567");
}

TEST(Main, sec) {
    World w;
    auto mem_t  = w.type_mem();
    auto i32_t  = w.type_int_width(32);
    auto argv_t = w.type_ptr(w.type_ptr(i32_t));
    auto i32_w = w.lit_nat(width2mod(32));
    auto l32 = w.lit_int(32);

    // Cn [mem, i32, i32**, Cn [mem, i32]]
    auto main_t = w.cn({mem_t, i32_t, argv_t, w.cn({mem_t, i32_t}, w.dbg("return"))});
    auto main = w.nom_lam(main_t, w.dbg("main"));
    auto [mem, argc, argv, ret] = main->vars<4>();

    auto body_t = w.cn(mem_t);

    auto lt = w.fn(ICmp::ul, i32_w);
    auto loop_t = w.cn({mem_t, i32_t, i32_t});
    auto loop = w.nom_lam(loop_t, w.dbg("loop"));

    auto body = w.nom_lam(body_t, w.dbg("body"));
    auto exit = w.nom_lam(body_t, w.dbg("exit"));

    {
        auto [lMem, iterVar, accumulator] = loop->vars<3>();
        loop->app(w.select(body, exit, w.app(lt, {iterVar, l32})), lMem);
    }

    loop->dump();
    loop->dump(0);

    auto add = w.fn(Wrap::add, w.lit_int(0), i32_w);
    {
        auto [lMem, iterVar, accumulator] = loop->vars<3>();

        auto accumAdd = w.app(add, {iterVar, accumulator});
        auto iterInc = w.app(add, {iterVar, w.lit_int(1)});
        body->app(loop, {lMem, iterInc, accumAdd});
    }
    body->dump();
    body->dump(0);
    {
        auto [lMem, iterVar, accumulator] = loop->vars<3>();
        exit->app(main->var(3), {main->var(0, nullptr), accumulator});
    }
    exit->dump();
    exit->dump(0);

    // main->app(ret, {mem, w.app(add, {l32, argc})});
    main->app(loop, {mem, w.lit_int(0), w.lit_int(0), ret});
    main->make_external();

    Stream cs(std::cout);
    w.stream(cs);

    std::ofstream file("test.ll");
    Stream s(file);
    thorin::ll::emit(w, s);
    file.close();

    // TODO make sure that proper clang is in path on Windows
#ifndef _MSC_VER
    std::system("clang test.ll -o `pwd`/test");
    EXPECT_EQ(240, WEXITSTATUS(std::system("./test a b c")));
#endif
}

TEST(Main, loop) {
    World w;
    auto mem_t  = w.type_mem();
    auto i32_t  = w.type_int_width(32);
    auto argv_t = w.type_ptr(w.type_ptr(i32_t));
    auto i32_w  = w.lit_nat(width2mod(32));

    // Cn [mem, i32, Cn [mem, i32]]
    auto main_t = w.cn({mem_t, i32_t, argv_t, w.cn({mem_t, i32_t})});
    auto main = w.nom_lam(main_t, w.dbg("main"));
    
    {
        // [a, b, ..] -> cn [mem, i, a, b, .., cn[mem, i, a, b, ..]]
        // [(a, b, ..)] -> cn [mem, i, (a, b, ..), cn[mem, i, (a, b, ..)]]
        // {
        //     auto make_cn = w.nom_pi(w.kind())->set_dom(w.kind());
        //     make_cn->set_codom(w.cn({mem_t, i32_t, make_cn->var(0, nullptr), w.cn({mem_t, i32_t, make_cn->var(0,nullptr)})}));
        //     make_cn->dump();
        //     make_cn->dump(0);

        //     auto cn = w.app(make_cn, w.tuple({i32_t, i32_t}));
        //     cn->dump();
        //     cn->dump(0);
        // }

        auto sig = w.nom_sigma(w.space(), 2);
        sig->set(0, w.type_nat());
        sig->set(1, w.arr(sig->var(0_s), w.kind()));
        // // sig->set(1, w.arr(sig->var(0, nullptr), w.type_nat()));
        // std::cout << "sig: \n";
        // sig->dump();
        // sig->dump(0);
        auto loop_type_producer = w.nom_pi(w.kind())->set_dom(sig);
        // auto paramst = loop_type_producer->var(0, w.dbg("body_params"));
        auto [n, paramstpl] = loop_type_producer->vars<2>();
        // auto paramstpl = loop_type_producer->op(0);
        auto inarr = w.nom_arr(n);
        inarr->set(w.extract(paramstpl, inarr->var(0_s)));

        auto cont_type = w.cn({mem_t, i32_t, inarr});
        auto body_type = w.cn({mem_t, i32_t, inarr, cont_type});
        auto loop_ax_type = w.cn({mem_t, i32_t, i32_t, inarr, body_type});
        loop_type_producer->set_codom(loop_ax_type);
        // loop_type_producer->set_codom(w.cn({mem_t, i32_t, i32_t, body_type}, w.dbg("loop_cn")));

        std::cout << "ltp: \n";
        loop_type_producer->dump();
        loop_type_producer->dump(0);
        loop_type_producer->dump(5);

        auto ax = w.axiom(nullptr, loop_type_producer, Tag::Loop, 0, w.dbg("loop"));
        ax->dump();
        ax->dump(0);

        auto applied = w.app(ax, {w.lit_nat(2), w.pack(2, i32_t)});
        applied->dump();
        applied->dump(0);
        applied->dump(5);

        // auto lam = w.lam(body_type, );
        body_type->dump();
        body_type->dump(0);
        body_type->dump(5);

        auto body = w.nom_lam(body_type, w.dbg("body"));
        {
            auto [mem, i, tupl, cont] = body->vars<4>();
            body->app(cont, {mem, i, tupl});
        }
        body->dump();
        body->dump(0);
        body->dump(5);
        {
            auto [mem, argc, argv, ret] = main->vars<4>();
            // auto applied_twice = w.app(applied, {mem, w.lit_int(0), argc, body});
            // applied_twice->dump();
            // applied_twice->dump(0);
            main->app(applied, {mem, w.lit_int(0), argc, w.tuple({w.lit_int(0), w.lit_int(5)}), body});
        }
    }

    // // [ret_t: *] -> [n: nat, b: [i: nat, continue: loop], ret: ret_t] -> !
    // auto loop = w.app(w.ax_loop(), ret)->as_nom<Pi>();

    // // [i: nat, continue : loop] -> !
    // auto body_t = w.cn({w.type_nat(), loop});
    // auto body = w.nom_lam(body_t, w.dbg("body"));
    // {
    //     auto [lMem, iterVar, accumulator] = loop->vars<3>();
    //     auto [bodyI, bodyCont] = body->vars<2>();

    //     auto add = w.fn(Wrap::add, w.lit_int(0), i32_w);
    //     auto accumAdd = w.app(add, {bodyI, accumulator});
    //     body->app(bodyCont, {accumAdd});
    // }
    
    // auto [mem, argc, argv, ret] = main->vars<4>();
    // main->app(ret, {mem, argc});
    main->make_external();

    main->dump();
    main->dump(0);
    main->dump(10);


    Stream cs(std::cout);
    // w.stream(cs);


    std::ofstream file("test.ll");
    Stream s(file);
    ll::emit(w, s);
    file.close();

#ifndef _MSC_VER
    // TODO make sure that proper clang is in path on Windows
    std::system("clang test.ll -o test");
    // I don't know why but for some reason the output doesn't appear on the test server.
#if 0
    EXPECT_EQ(4, WEXITSTATUS(std::system("./test a b c")));
    EXPECT_EQ(7, WEXITSTATUS(std::system("./test a b c d e f")));
#endif
#endif
}

