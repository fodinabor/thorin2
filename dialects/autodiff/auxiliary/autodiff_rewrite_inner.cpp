#include "dialects/autodiff/autodiff.h"
#include "dialects/autodiff/auxiliary/autodiff_aux.h"
#include "dialects/autodiff/passes/autodiff_eval.h"
#include "dialects/direct/direct.h"
#include "dialects/core/core.h"

namespace thorin::autodiff {

const Def* op_cps2ds(const Def* f) {
    auto& world = f->world();
    // TODO: assert continuation
    auto f_ty = f->type()->as<Pi>();
    auto T    = f_ty->dom(0);
    auto U    = f_ty->dom(1)->as<Pi>()->dom();
    // TODO: check if app can be used instead of raw_app
    return world.raw_app(world.raw_app(world.ax<direct::cps2ds>(), {T, U}), f);
}

const Def* op_sum(DefArray defs) {
    // TODO: assert all are of type T
    auto& world = defs[0]->world();
    auto T      = defs[0]->type();
    return world.raw_app(world.raw_app(world.ax<sum>(), {world.lit_nat(defs.size()), T}), world.tuple(defs));
}


#define f_arg_ty f->type()->dom(0)

const Def* AutoDiffEval::augment_lit(const Lit* lit, Lam* f, Lam* f_diff) {
    auto& world = lit->world();

    auto aug_lit = lit;
    // set zero pullback
    auto pb                   = zero_pullback(lit->type(), f_arg_ty);
    partial_pullback[aug_lit] = pb;
    return lit;
}

const Def* AutoDiffEval::augment_var(const Var* var, Lam* f, Lam* f_diff) {
    auto& world = var->world();
    assert(augmented.count(var));
    auto aug_var = augmented[var];
    assert(partial_pullback.count(aug_var));
    return var;
}

const Def* AutoDiffEval::augment_extract(const Extract* ext, Lam* f, Lam* f_diff) {
    auto& world = ext->world();

    auto tuple = ext->tuple();
    auto index = ext->index();

    auto aug_tuple = augment(tuple, f, f_diff);
    auto aug_index = augment(index, f, f_diff);

    // TODO: if not exists use:
    // e:T, b:B
    // b = e#i
    // b* = \lambda (s:B). e* (insert s at i in (zero T))

    const Def* pb;
    world.DLOG("tuple was: {} : {}", aug_tuple, aug_tuple->type());
    if (shadow_pullback.count(aug_tuple)) {
        auto shadow_tuple_pb = shadow_pullback[aug_tuple];
        world.DLOG("Shadow pullback: {} : {}", shadow_tuple_pb, shadow_tuple_pb->type());
        pb = world.extract(shadow_tuple_pb, aug_index);
    } else {
        assert(partial_pullback.count(aug_tuple));
        auto tuple_pb = partial_pullback[aug_tuple];
        auto pb_ty    = pullback_type(ext->type(), f_arg_ty);
        auto pb_fun   = world.nom_lam(pb_ty, world.dbg("extract_pb"));
        world.DLOG("Pullback: {} : {}", pb_fun, pb_fun->type());
        auto pb_tangent = pb_fun->var((nat_t)0, world.dbg("s"));
        auto tuple_tan  = world.insert(op_zero(aug_tuple->type()), aug_index, pb_tangent, world.dbg("tup_s"));
        pb_fun->app(true, tuple_pb,
                    {
                        tuple_tan,
                        pb_fun->var(1) // ret_var but make sure to select correct one
                    });
        pb = pb_fun;
    }

    auto aug_ext              = world.extract(aug_tuple, aug_index);
    partial_pullback[aug_ext] = pb;

    return aug_ext;
}

const Def* AutoDiffEval::augment_tuple(const Tuple* tup, Lam* f, Lam* f_diff) {
    auto& world = tup->world();

    // augment ops

    // TODO: should use ops instead?
    DefArray aug_ops(tup->projs(), [&](const Def* op) { return augment(op, f, f_diff); });
    auto aug_tup = world.tuple(aug_ops);

    DefArray pbs(aug_ops, [&](const Def* op) { return partial_pullback[op]; });
    // create shadow pb
    auto shadow_pb           = world.tuple(pbs);
    shadow_pullback[aug_tup] = shadow_pb;

    // create partial pb
    // \lambda (s:[E0,...,Em]).
    //    sum (m,A)
    //      ((cps2ds e0*) (s#0), ..., (cps2ds em*) (s#m))
    auto pb_ty = pullback_type(tup->type(), f_arg_ty);
    auto pb    = world.nom_lam(pb_ty, world.dbg("tup_pb"));
    world.DLOG("Augmented tuple: {} : {}", aug_tup, aug_tup->type());
    world.DLOG("Tuple Pullback: {} : {}", pb, pb->type());

    auto pb_tangent = pb->var((nat_t)0, world.dbg("tup_s"));

    // TODO: move op_cps2ds to direct dialect and merge then
    DefArray tangents(pbs.size(), [&](nat_t i) { return world.app(op_cps2ds(pbs[i]), world.extract(pb_tangent, i)); });
    pb->app(true, pb->var(1),
            // summed up tangents
            op_sum(tangents));
    partial_pullback[aug_tup] = pb;

    return aug_tup;
}

const Def* AutoDiffEval::augment_app(const App* app, Lam* f, Lam* f_diff) {
    auto& world = app->world();

    auto callee = app->callee();
    auto arg    = app->arg();

    auto aug_arg    = augment(arg, f, f_diff);
    auto aug_callee = augment(callee, f, f_diff);
    // auto arg_ppb    = partial_pullback[aug_arg];

    if (is_open_continuation(callee)) {
        // TODO: check if function (not operator)
        // original function = unclosed function (return cont / continuation)
        //   Cn[E]
        // aug_calle (looks like a function but is not really)
        //   Cn[E, Cn[E, Cn[A]]]

        // ret(e) => ret'(e, e*)

        world.DLOG("continuation {} : {} => {} : {}", callee, callee->type(), aug_callee, aug_callee->type());

        auto arg_pb  = partial_pullback[aug_arg];
        auto aug_app = world.app(aug_callee, {aug_arg, arg_pb});
        world.DLOG("Augmented application: {} : {}", aug_app, aug_app->type());
        // assert(false);
        return aug_app;
    }

    // TODO: handle cascading functions
    // TODO: handle axiom app before or after augment

    // return def;

    assert(false);
}

/// rewrite the given definition
///
const Def* AutoDiffEval::augment_(const Def* def, Lam* f, Lam* f_diff) {
    auto& world   = def->world();
    // for types holds:
    // we use macros above to avoid recomputation
    // TODO: alternative: use class instance to rewrite inside a function and save such values (f, f_diff, f_arg_ty)
    // f_arg_ty = f->type()->dom(0);
    // f_arg_tangent_ty = tangent_type_fun(f_arg_ty);
    // f_arg_tangent_ty =
    //     f_diff->type()->dom(1)->as<Pi>() // return type
    //     ->dom(1)->as<Pi>() // pb type
    //     ->dom(1)->as<Pi>()->dom(); // arg tangent type

    world.DLOG("Augment def {} : {}", def, def->type());

    // app => cont, operator, function
    if (auto app = def->isa<App>()) {
        auto callee = app->callee();
        auto arg    = app->arg();
        world.DLOG("Augment application: app {} with {}", callee, arg);
        return augment_app(app, f, f_diff);
    }

    // projection
    else if (auto ext = def->isa<Extract>()) {
        // world.DLOG("Augment extract: {}", def);
        auto tuple = ext->tuple();
        auto index = ext->index();
        world.DLOG("Augment extract: {} #[{}]", tuple, index);
        return augment_extract(ext, f, f_diff);
    }

    // vars (function argument)
    else if (auto var = def->isa<Var>()) {
        world.DLOG("Augment variable: {}", var);
        return augment_var(var, f, f_diff);
    }

    // constants
    else if (auto lit = def->isa<Lit>()) {
        world.DLOG("Augment literal: {}", def);
        return augment_lit(lit, f, f_diff);
    }

    // tuple
    else if (auto tup = def->isa<Tuple>()) {
        world.DLOG("Augment tuple: {}", def);
        return augment_tuple(tup, f, f_diff);
    }

    //axiom
    // TODO: move concrete handling to own file, directory
    else if(auto ax = def->isa<Axiom>()) {
        world.DLOG("Augment axiom: {}", ax);
        world.DLOG("axiom curry: {}", ax->curry());
        world.DLOG("axiom flags: {}", ax->flags());
        // world.DLOG("core::wrap::AxiomBase: {}", core::wrap::Axiom_Base);
        // world.DLOG("core::wrap::mul: {}", core::wrap::mul);
        // world.DLOG("core::wrap::mul: {}", 0x1104c60000000502);
        // return augment_axiom(ax, f, f_diff);

        // auto mul = match<core::wrap::mul>(ax);

        // does not work
        auto wrap = match<core::wrap>(ax);
        if(wrap)
            world.DLOG("match wrap axiom");

        // does not work
        auto amul = match<core::wrap>(
            core::wrap::mul,
            ax);
        if(amul)
            world.DLOG("match mul axiom");

        // error with axiom tags
        auto amul2 = raw_match<core::wrap>(
            core::wrap::mul,
            ax);
        if(amul2)
            world.DLOG("raw match mul axiom");

        // if ((ax->flags() & ~0xFF_u64) == detail::base_value<core::wrap::mul>()) {

        // }

        // equivalent to above
        if(ax->flags()==core::wrap::mul) {
            world.DLOG("multiplication axiom flags");
        }
        // if(ax->flags()==core::wrap::Axiom_Base) {
        //     world.DLOG("wrap axiom");
        // }

        assert(false);
    }

    // TODO: remaining (lambda, axiom)

    world.ELOG("did not expect to augment: {} : {}", def, def->type());
    world.ELOG("node: {}", def->node_name());
    assert(false && "augment not implemented on this def");
}

} // namespace thorin::autodiff