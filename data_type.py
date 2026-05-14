"""Utilities for encoded datatypes and subtype packages.

This module holds the reusable plumbing that was previously scattered across
``nat0.py``, ``hf_sets.py``, ``hf_syntax.py``, and the SK-term setup in
``halting.py``:

* registering a basic HOL subtype and its parser aliases;
* defining constructor constants together with pointwise ``_AT`` equations;
* proving size lemmas for binary constructors encoded as
  ``Pair_ord tag (Pair_ord a b)``;
* proving the common monotonicity step for binary recursive recognizer
  branches;
* unfolding ``define_wf_lt`` recursion equations through their helper body.

The functions here deliberately avoid owning a full datatype story. They are
small proof-producing building blocks that datatype packages can compose.
"""

import dataclasses
from collections import namedtuple

from fusion import Var, ASSUME, EQ_MP, DEDUCT_ANTISYM_RULE, vsubst, INST_TYPE, ABS
from fusion import mk_type, new_basic_type_definition
from basics import mk_const, mk_abs, mk_app, mk_eq, dest_eq, is_eq, rator, rand
from parser import add_const, add_type, define, parse_type
from axioms import (
    F,
    mk_and,
    mk_exists,
    mk_not,
    mk_select,
    dest_conj,
    dest_exists,
    dest_forall,
    dest_imp,
    dest_disj,
    SELECT_AX,
    aty,
)
from axioms import mk_or
from proof import proof, define_with_at
from tactics import (
    SPEC,
    SPECL,
    SYM,
    MP,
    CHOOSE_WITNESS,
    CONJ,
    CONJUNCT1,
    CONJUNCT2,
    EXISTS,
    AP_THM,
    AP_TERM,
    REWRITE_RULE,
    REWRITE_CONV,
    TRANS,
    DISCH,
    CONTR,
    NOT_ELIM,
    EQF_INTRO,
    DISJ1,
    DISJ2,
    DISJ_CASES,
    BETA_CONV,
    BETA_NORM,
    REFL,
    GEN,
    GENL,
)
from tactics import or_chain_collapse


@dataclasses.dataclass(frozen=True)
class BasicSubtype:
    """Result of ``define_basic_subtype``."""

    ty: object
    abs_const: object
    rep_const: object
    abs_rep: object
    rep_abs: object


def define_basic_subtype(tyname, abs_rep_names, existence_thm):
    """Introduce a HOL subtype and register its parser aliases.

    This is a thin wrapper over ``new_basic_type_definition``. It keeps the
    kernel theorem shape unchanged while returning the common values that every
    subtype setup immediately reconstructs by hand.
    """

    abs_rep, rep_abs = new_basic_type_definition(tyname, abs_rep_names, existence_thm)
    ty = mk_type(tyname, [])
    abs_name, rep_name = abs_rep_names
    abs_const = mk_const(abs_name, [])
    rep_const = mk_const(rep_name, [])
    add_type(tyname, ty)
    add_const(abs_name, abs_const)
    add_const(rep_name, rep_const)
    return BasicSubtype(ty, abs_const, rep_const, abs_rep, rep_abs)


@dataclasses.dataclass(frozen=True)
class ConstructorDef:
    """A defined constructor plus its pointwise equation."""

    name: str
    const: object
    def_thm: object
    at_thm: object


@dataclasses.dataclass(frozen=True)
class Nat0BinaryClosurePredicate:
    """Recognizer package for ``atoms | binary recursive constructor``."""

    name: str
    pred: object
    body_def: object
    body_const: object
    mono: object
    def_thm: object
    rec_raw: object
    rec: object
    atom_intros: list
    binary_intro: object


def define_constructor(name, ty, body, *, sig=None, infix=None, prefix=False, **bindings):
    """Define a constructor-like constant and derive its applied equation."""

    def_thm, at_thm = define_with_at(
        name, ty, body, sig=sig, infix=infix, prefix=prefix, **bindings
    )
    return ConstructorDef(name, mk_const(name, []), def_thm, at_thm)


def prove_pairord_binary_size_left(
    thm_name,
    var_l,
    var_r,
    ctor_name,
    ctor_at,
    tag_str,
    pair_lt_l,
    pair_lt_r,
    lt_trans,
):
    """Build ``|- !a b. nat0_lt a (Ctor a b)`` for Pair_ord-tagged binary ctors."""

    @proof
    def _THM(p):
        from tactics import SPECL

        p.goal(f"!{var_l} {var_r}. nat0_lt {var_l} ({ctor_name} {var_l} {var_r})")
        p.fix(f"{var_l} {var_r}")
        ctor_at_inst = SPECL([p._parse(var_l), p._parse(var_r)], ctor_at)
        p.have(f"h1: nat0_lt {var_l} (Pair_ord {var_l} {var_r})").by(
            pair_lt_l, var_l, var_r
        )
        p.have(
            f"h2: nat0_lt (Pair_ord {var_l} {var_r}) "
            f"(Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(pair_lt_r, f"({tag_str})", f"Pair_ord {var_l} {var_r}")
        p.have(
            f"h3: nat0_lt {var_l} (Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(
            lt_trans,
            var_l,
            f"Pair_ord {var_l} {var_r}",
            f"Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r})",
            "h1",
            "h2",
        )
        p.thus(f"nat0_lt {var_l} ({ctor_name} {var_l} {var_r})").by_rewrite_of(
            "h3", [SYM(ctor_at_inst)]
        )

    return _THM


def prove_pairord_binary_size_right(
    thm_name,
    var_l,
    var_r,
    ctor_name,
    ctor_at,
    tag_str,
    pair_lt_r,
    lt_trans,
):
    """Build ``|- !a b. nat0_lt b (Ctor a b)`` for Pair_ord-tagged binary ctors."""

    @proof
    def _THM(p):
        from tactics import SPECL

        p.goal(f"!{var_l} {var_r}. nat0_lt {var_r} ({ctor_name} {var_l} {var_r})")
        p.fix(f"{var_l} {var_r}")
        ctor_at_inst = SPECL([p._parse(var_l), p._parse(var_r)], ctor_at)
        p.have(f"h1: nat0_lt {var_r} (Pair_ord {var_l} {var_r})").by(
            pair_lt_r, var_l, var_r
        )
        p.have(
            f"h2: nat0_lt (Pair_ord {var_l} {var_r}) "
            f"(Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(pair_lt_r, f"({tag_str})", f"Pair_ord {var_l} {var_r}")
        p.have(
            f"h3: nat0_lt {var_r} (Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(
            lt_trans,
            var_r,
            f"Pair_ord {var_l} {var_r}",
            f"Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r})",
            "h1",
            "h2",
        )
        p.thus(f"nat0_lt {var_r} ({ctor_name} {var_l} {var_r})").by_rewrite_of(
            "h3", [SYM(ctor_at_inst)]
        )

    return _THM


# Backwards-compatible names for older modules that still import the helpers
# directly. New code should use the public prove_pairord_* names above.
def _proof_lt_binary_left(thm_name, var_l, var_r, ctor_name, ctor_at, tag_str):
    from hf_sets import NAT0_LT_PAIR_ORD_L, NAT0_LT_PAIR_ORD_R
    from nat0_order import NAT0_LT_TRANS

    return prove_pairord_binary_size_left(
        thm_name,
        var_l,
        var_r,
        ctor_name,
        ctor_at,
        tag_str,
        NAT0_LT_PAIR_ORD_L,
        NAT0_LT_PAIR_ORD_R,
        NAT0_LT_TRANS,
    )


def _proof_lt_binary_right(thm_name, var_l, var_r, ctor_name, ctor_at, tag_str):
    from hf_sets import NAT0_LT_PAIR_ORD_R
    from nat0_order import NAT0_LT_TRANS

    return prove_pairord_binary_size_right(
        thm_name,
        var_l,
        var_r,
        ctor_name,
        ctor_at,
        tag_str,
        NAT0_LT_PAIR_ORD_R,
        NAT0_LT_TRANS,
    )


def _extract_nfg(hyp_th):
    """Pull n, f, g out of ``|- !k. nat0_lt k n ==> f k = g k``."""

    forall_pred = dest_forall(hyp_th._concl)
    if forall_pred is None:
        raise ValueError(f"_extract_nfg: hyp_th not !k. ...; got {hyp_th._concl}")
    imp_parts = dest_imp(forall_pred.body)
    if imp_parts is None:
        raise ValueError(
            f"_extract_nfg: hyp body not implication; got {forall_pred.body}"
        )
    ant, conseq = imp_parts
    n_t = rand(ant)
    fk, gk = dest_eq(conseq)
    return n_t, rator(fk), rator(gk), forall_pred.bvar.ty


def mono_iff_unary_step(ctor, size_lemma, hyp_th):
    """Per-disjunct iff for a unary recursive recognizer case."""

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    x_var = Var("x", k_ty)
    n_eq_ctor_x = mk_eq(n_t, mk_app(ctor, x_var))
    body_l = mk_and(n_eq_ctor_x, mk_app(f_t, x_var))
    body_r = mk_and(n_eq_ctor_x, mk_app(g_t, x_var))
    pred_l = mk_abs(x_var, body_l)
    pred_r = mk_abs(x_var, body_r)
    LHS = mk_exists(x_var, body_l)
    RHS = mk_exists(x_var, body_r)

    chosen_l = CHOOSE_WITNESS(pred_l, ASSUME(LHS))
    n_eq_l = CONJUNCT1(chosen_l)
    fw_th = CONJUNCT2(chosen_l)
    w_t = rand(rand(n_eq_l._concl))
    sl_at_w = SPEC(w_t, size_lemma)
    lt_w_n = REWRITE_RULE([SYM(n_eq_l)], sl_at_w)
    fw_eq_gw = MP(SPEC(w_t, hyp_th), lt_w_n)
    gw_th = EQ_MP(fw_eq_gw, fw_th)
    R_th = EXISTS(pred_r, w_t, CONJ(n_eq_l, gw_th))

    chosen_r = CHOOSE_WITNESS(pred_r, ASSUME(RHS))
    n_eq_r = CONJUNCT1(chosen_r)
    gw2_th = CONJUNCT2(chosen_r)
    w2_t = rand(rand(n_eq_r._concl))
    sl_at_w2 = SPEC(w2_t, size_lemma)
    lt_w2_n = REWRITE_RULE([SYM(n_eq_r)], sl_at_w2)
    fw2_eq_gw2 = MP(SPEC(w2_t, hyp_th), lt_w2_n)
    fw2_th = EQ_MP(SYM(fw2_eq_gw2), gw2_th)
    L_th = EXISTS(pred_l, w2_t, CONJ(n_eq_r, fw2_th))

    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def mono_iff_binary_step(ctor, size_lemma_l, size_lemma_r, hyp_th):
    """Per-disjunct iff for a binary recursive recognizer case.

    Returns
    ``|- (?a b. n = ctor a b /\\ f a /\\ f b)
          = (?a b. n = ctor a b /\\ g a /\\ g b)``,
    reading ``n``, ``f``, and ``g`` from ``hyp_th``.
    """

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    a_var = Var("a", k_ty)
    b_var = Var("b", k_ty)

    def _bodies(fn):
        ctor_ab = mk_app(ctor, a_var, b_var)
        return mk_and(
            mk_eq(n_t, ctor_ab),
            mk_and(mk_app(fn, a_var), mk_app(fn, b_var)),
        )

    body_inner_l = _bodies(f_t)
    body_inner_r = _bodies(g_t)
    LHS = mk_exists(a_var, mk_exists(b_var, body_inner_l))
    RHS = mk_exists(a_var, mk_exists(b_var, body_inner_r))

    def _direction(src, target_inner_body, swap_fg):
        h_top = ASSUME(src)
        outer_pred = dest_exists(src)
        chosen_outer = CHOOSE_WITNESS(outer_pred, h_top)
        new_inner_pred = dest_exists(chosen_outer._concl)
        chosen_inner = CHOOSE_WITNESS(new_inner_pred, chosen_outer)
        n_eq_th = CONJUNCT1(chosen_inner)
        rest = CONJUNCT2(chosen_inner)
        ha_th = CONJUNCT1(rest)
        hb_th = CONJUNCT2(rest)
        ctor_app = rand(n_eq_th._concl)
        w_b = rand(ctor_app)
        w_a = rand(rator(ctor_app))
        sl_a = SPEC(w_b, SPEC(w_a, size_lemma_l))
        sl_b = SPEC(w_b, SPEC(w_a, size_lemma_r))
        lt_a_n = REWRITE_RULE([SYM(n_eq_th)], sl_a)
        lt_b_n = REWRITE_RULE([SYM(n_eq_th)], sl_b)
        eq_a = MP(SPEC(w_a, hyp_th), lt_a_n)
        eq_b = MP(SPEC(w_b, hyp_th), lt_b_n)
        if swap_fg:
            ha_out = EQ_MP(SYM(eq_a), ha_th)
            hb_out = EQ_MP(SYM(eq_b), hb_th)
        else:
            ha_out = EQ_MP(eq_a, ha_th)
            hb_out = EQ_MP(eq_b, hb_th)
        new_body = CONJ(n_eq_th, CONJ(ha_out, hb_out))
        target_outer_pred_body = mk_abs(a_var, mk_exists(b_var, target_inner_body))
        inner_pred_aw = mk_abs(
            b_var,
            mk_and(
                mk_eq(n_t, mk_app(ctor, w_a, b_var)),
                mk_and(
                    mk_app(g_t if not swap_fg else f_t, w_a),
                    mk_app(g_t if not swap_fg else f_t, b_var),
                ),
            ),
        )
        inner_th = EXISTS(inner_pred_aw, w_b, new_body)
        return EXISTS(target_outer_pred_body, w_a, inner_th)

    R_th = _direction(LHS, body_inner_r, swap_fg=False)
    L_th = _direction(RHS, body_inner_l, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def mono_iff_binary_right_step(ctor, size_lemma_r, hyp_th):
    """Per-disjunct iff where only the right argument is recursive."""

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    a_var = Var("a", k_ty)
    b_var = Var("b", k_ty)

    def _bodies(fn):
        ctor_ab = mk_app(ctor, a_var, b_var)
        return mk_and(mk_eq(n_t, ctor_ab), mk_app(fn, b_var))

    body_inner_l = _bodies(f_t)
    body_inner_r = _bodies(g_t)
    LHS = mk_exists(a_var, mk_exists(b_var, body_inner_l))
    RHS = mk_exists(a_var, mk_exists(b_var, body_inner_r))

    def _direction(src, target_inner_body, swap_fg):
        h_top = ASSUME(src)
        outer_pred = dest_exists(src)
        chosen_outer = CHOOSE_WITNESS(outer_pred, h_top)
        new_inner_pred = dest_exists(chosen_outer._concl)
        chosen_inner = CHOOSE_WITNESS(new_inner_pred, chosen_outer)
        n_eq_th = CONJUNCT1(chosen_inner)
        hb_th = CONJUNCT2(chosen_inner)
        ctor_app = rand(n_eq_th._concl)
        w_b = rand(ctor_app)
        w_a = rand(rator(ctor_app))
        sl_b = SPEC(w_b, SPEC(w_a, size_lemma_r))
        lt_b_n = REWRITE_RULE([SYM(n_eq_th)], sl_b)
        eq_b = MP(SPEC(w_b, hyp_th), lt_b_n)
        hb_out = EQ_MP(SYM(eq_b) if swap_fg else eq_b, hb_th)
        new_body = CONJ(n_eq_th, hb_out)
        target_outer_pred_body = mk_abs(a_var, mk_exists(b_var, target_inner_body))
        inner_pred_aw = mk_abs(
            b_var,
            mk_and(
                mk_eq(n_t, mk_app(ctor, w_a, b_var)),
                mk_app(g_t if not swap_fg else f_t, b_var),
            ),
        )
        inner_th = EXISTS(inner_pred_aw, w_b, new_body)
        return EXISTS(target_outer_pred_body, w_a, inner_th)

    R_th = _direction(LHS, body_inner_r, swap_fg=False)
    L_th = _direction(RHS, body_inner_l, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def mono_iff_unary_pw_step(ctor, size_lemma, hyp_th, v_term):
    """Pointwise unary recursive case for function-valued predicates."""

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    x_var = Var("x", k_ty)
    n_eq_ctor_x = mk_eq(n_t, mk_app(ctor, x_var))
    body_l = mk_and(n_eq_ctor_x, mk_app(f_t, x_var, v_term))
    body_r = mk_and(n_eq_ctor_x, mk_app(g_t, x_var, v_term))
    pred_l = mk_abs(x_var, body_l)
    pred_r = mk_abs(x_var, body_r)
    LHS = mk_exists(x_var, body_l)
    RHS = mk_exists(x_var, body_r)

    chosen_l = CHOOSE_WITNESS(pred_l, ASSUME(LHS))
    n_eq_l = CONJUNCT1(chosen_l)
    fxv_th = CONJUNCT2(chosen_l)
    w_t = rand(rand(n_eq_l._concl))
    sl_at_w = SPEC(w_t, size_lemma)
    lt_w_n = REWRITE_RULE([SYM(n_eq_l)], sl_at_w)
    fw_eq_gw = MP(SPEC(w_t, hyp_th), lt_w_n)
    gxv_th = EQ_MP(AP_THM(fw_eq_gw, v_term), fxv_th)
    R_th = EXISTS(pred_r, w_t, CONJ(n_eq_l, gxv_th))

    chosen_r = CHOOSE_WITNESS(pred_r, ASSUME(RHS))
    n_eq_r = CONJUNCT1(chosen_r)
    gxv2_th = CONJUNCT2(chosen_r)
    w2_t = rand(rand(n_eq_r._concl))
    sl_at_w2 = SPEC(w2_t, size_lemma)
    lt_w2_n = REWRITE_RULE([SYM(n_eq_r)], sl_at_w2)
    fw2_eq_gw2 = MP(SPEC(w2_t, hyp_th), lt_w2_n)
    fxv2_th = EQ_MP(SYM(AP_THM(fw2_eq_gw2, v_term)), gxv2_th)
    L_th = EXISTS(pred_l, w2_t, CONJ(n_eq_r, fxv2_th))

    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def _mono_iff_binary_pw_step(
    ctor, size_lemma_l, size_lemma_r, hyp_th, v_term, rest_builder, recurses_l
):
    """Generic binary pointwise MONO step."""

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    a_var = Var("a", k_ty)
    b_var = Var("b", k_ty)

    def _bodies(fn):
        ctor_ab = mk_app(ctor, a_var, b_var)
        return mk_and(mk_eq(n_t, ctor_ab), rest_builder(fn, a_var, b_var, v_term))

    body_inner_l = _bodies(f_t)
    body_inner_r = _bodies(g_t)
    LHS = mk_exists(a_var, mk_exists(b_var, body_inner_l))
    RHS = mk_exists(a_var, mk_exists(b_var, body_inner_r))

    def _direction(src, target_inner_body, swap_fg):
        h_top = ASSUME(src)
        outer_pred = dest_exists(src)
        chosen_outer = CHOOSE_WITNESS(outer_pred, h_top)
        new_inner_pred = dest_exists(chosen_outer._concl)
        chosen_inner = CHOOSE_WITNESS(new_inner_pred, chosen_outer)
        n_eq_th = CONJUNCT1(chosen_inner)
        rest = CONJUNCT2(chosen_inner)
        ctor_app = rand(n_eq_th._concl)
        w_b = rand(ctor_app)
        w_a = rand(rator(ctor_app))
        rewrites = []
        if recurses_l:
            sl_a = SPEC(w_b, SPEC(w_a, size_lemma_l))
            lt_a_n = REWRITE_RULE([SYM(n_eq_th)], sl_a)
            rewrites.append(AP_THM(MP(SPEC(w_a, hyp_th), lt_a_n), v_term))
        sl_b = SPEC(w_b, SPEC(w_a, size_lemma_r))
        lt_b_n = REWRITE_RULE([SYM(n_eq_th)], sl_b)
        rewrites.append(AP_THM(MP(SPEC(w_b, hyp_th), lt_b_n), v_term))
        if swap_fg:
            rewrites = [SYM(r) for r in rewrites]
        rest_out = REWRITE_RULE(rewrites, rest)
        new_body = CONJ(n_eq_th, rest_out)
        target_fn = g_t if not swap_fg else f_t
        target_outer_pred_body = mk_abs(a_var, mk_exists(b_var, target_inner_body))
        inner_pred_aw = mk_abs(
            b_var,
            mk_and(
                mk_eq(n_t, mk_app(ctor, w_a, b_var)),
                rest_builder(target_fn, w_a, b_var, v_term),
            ),
        )
        inner_th = EXISTS(inner_pred_aw, w_b, new_body)
        return EXISTS(target_outer_pred_body, w_a, inner_th)

    R_th = _direction(LHS, body_inner_r, swap_fg=False)
    L_th = _direction(RHS, body_inner_l, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def mono_iff_binary_disj_pw_step(ctor, size_lemma_l, size_lemma_r, hyp_th, v_term):
    """Pointwise binary case whose recursive facts are joined by disjunction."""

    return _mono_iff_binary_pw_step(
        ctor,
        size_lemma_l,
        size_lemma_r,
        hyp_th,
        v_term,
        rest_builder=lambda fn, a, b, v: mk_or(mk_app(fn, a, v), mk_app(fn, b, v)),
        recurses_l=True,
    )


def mono_iff_eq_or_pw_step(ctor, size_lemma_r, hyp_th, v_term):
    r"""Pointwise right-recursive case ``x = head \/ f tail x``."""

    return _mono_iff_binary_pw_step(
        ctor,
        None,
        size_lemma_r,
        hyp_th,
        v_term,
        rest_builder=lambda fn, a, b, v: mk_or(mk_eq(v, a), mk_app(fn, b, v)),
        recurses_l=False,
    )


def _ap_thm_chain(eq_th, args):
    """Apply a function equality theorem to each term in ``args``."""

    out = eq_th
    for arg in args:
        out = AP_THM(out, arg)
    return out


def mono_iff_value_unary_pw_step(ctor, size_lemma, hyp_th, args, r_term, value_fn):
    """Unary value-shape pointwise MONO step."""

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    x_var = Var("x", k_ty)
    n_eq_ctor_x = mk_eq(n_t, mk_app(ctor, x_var))

    def _body(fn):
        return mk_and(n_eq_ctor_x, mk_eq(r_term, value_fn(mk_app(fn, x_var, *args))))

    body_l = _body(f_t)
    body_r = _body(g_t)
    pred_l = mk_abs(x_var, body_l)
    pred_r = mk_abs(x_var, body_r)
    LHS = mk_exists(x_var, body_l)
    RHS = mk_exists(x_var, body_r)

    def _direction(src_pred, src_term, target_pred, swap_fg):
        chosen = CHOOSE_WITNESS(src_pred, ASSUME(src_term))
        n_eq_th = CONJUNCT1(chosen)
        val_eq_th = CONJUNCT2(chosen)
        w_t = rand(rand(n_eq_th._concl))
        sl_at_w = SPEC(w_t, size_lemma)
        lt_w_n = REWRITE_RULE([SYM(n_eq_th)], sl_at_w)
        fw_eq_gw = MP(SPEC(w_t, hyp_th), lt_w_n)
        rewrite = _ap_thm_chain(fw_eq_gw, args)
        if swap_fg:
            rewrite = SYM(rewrite)
        return EXISTS(target_pred, w_t, CONJ(n_eq_th, REWRITE_RULE([rewrite], val_eq_th)))

    R_th = _direction(pred_l, LHS, pred_r, swap_fg=False)
    L_th = _direction(pred_r, RHS, pred_l, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def _mono_iff_value_binary_pw_step(
    ctor, size_lemma_l, size_lemma_r, hyp_th, args, rest_builder, recurses_l
):
    """Generic binary value-shape pointwise MONO step."""

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    a_var = Var("a", k_ty)
    b_var = Var("b", k_ty)

    def _bodies(fn):
        ctor_ab = mk_app(ctor, a_var, b_var)
        return mk_and(mk_eq(n_t, ctor_ab), rest_builder(fn, a_var, b_var, args))

    body_inner_l = _bodies(f_t)
    body_inner_r = _bodies(g_t)
    LHS = mk_exists(a_var, mk_exists(b_var, body_inner_l))
    RHS = mk_exists(a_var, mk_exists(b_var, body_inner_r))

    def _direction(src, target_inner_body, target_fn, swap_fg):
        h_top = ASSUME(src)
        outer_pred = dest_exists(src)
        chosen_outer = CHOOSE_WITNESS(outer_pred, h_top)
        new_inner_pred = dest_exists(chosen_outer._concl)
        chosen_inner = CHOOSE_WITNESS(new_inner_pred, chosen_outer)
        n_eq_th = CONJUNCT1(chosen_inner)
        rest = CONJUNCT2(chosen_inner)
        ctor_app = rand(n_eq_th._concl)
        w_b = rand(ctor_app)
        w_a = rand(rator(ctor_app))
        rewrites = []
        if recurses_l:
            sl_a = SPEC(w_b, SPEC(w_a, size_lemma_l))
            lt_a_n = REWRITE_RULE([SYM(n_eq_th)], sl_a)
            rewrites.append(_ap_thm_chain(MP(SPEC(w_a, hyp_th), lt_a_n), args))
        sl_b = SPEC(w_b, SPEC(w_a, size_lemma_r))
        lt_b_n = REWRITE_RULE([SYM(n_eq_th)], sl_b)
        rewrites.append(_ap_thm_chain(MP(SPEC(w_b, hyp_th), lt_b_n), args))
        if swap_fg:
            rewrites = [SYM(r) for r in rewrites]
        rest_out = REWRITE_RULE(rewrites, rest)
        new_body = CONJ(n_eq_th, rest_out)
        target_outer_pred_body = mk_abs(a_var, mk_exists(b_var, target_inner_body))
        inner_pred_aw = mk_abs(
            b_var,
            mk_and(
                mk_eq(n_t, mk_app(ctor, w_a, b_var)),
                rest_builder(target_fn, w_a, b_var, args),
            ),
        )
        inner_th = EXISTS(inner_pred_aw, w_b, new_body)
        return EXISTS(target_outer_pred_body, w_a, inner_th)

    R_th = _direction(LHS, body_inner_r, g_t, swap_fg=False)
    L_th = _direction(RHS, body_inner_l, f_t, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def mono_iff_value_binary_pw_step(
    ctor, size_lemma_l, size_lemma_r, hyp_th, args, r_term, value_fn
):
    """Binary value-shape pointwise MONO step."""

    return _mono_iff_value_binary_pw_step(
        ctor,
        size_lemma_l,
        size_lemma_r,
        hyp_th,
        args,
        rest_builder=lambda fn, a, b, ags: mk_eq(
            r_term,
            value_fn(mk_app(fn, a, *ags), mk_app(fn, b, *ags)),
        ),
        recurses_l=True,
    )


def unfold_rec_via_body_def(rec_raw, body_def):
    """Convert ``|- !n. fn n = F fn n`` to ``|- !n. fn n = body[fn,n]``."""

    forall_pred = dest_forall(rec_raw._concl)
    n_local = forall_pred.bvar
    spec = SPEC(n_local, rec_raw)
    rhs = rand(spec._concl)
    eq_unfold = REWRITE_CONV([body_def], rhs)
    eq_beta = BETA_NORM(rand(eq_unfold._concl))
    rhs_eq = TRANS(eq_unfold, eq_beta)
    return GEN(n_local, TRANS(spec, rhs_eq))


def _unfold_rec_via_F_def(rec_raw, F_def):
    """Compatibility alias for the historical helper name."""

    return unfold_rec_via_body_def(rec_raw, F_def)


def _select_collapse_eq(K_t, r_var):
    """Build ``|- (@r. r = K) = K``."""

    pred = mk_abs(r_var, mk_eq(r_var, K_t))
    sel_ax_at = INST_TYPE([(r_var.ty, aty)], SELECT_AX)
    spec_p = SPEC(pred, sel_ax_at)
    spec_x = SPEC(K_t, spec_p)
    bridge_K = BETA_CONV(mk_app(pred, K_t))
    p_K_th = EQ_MP(SYM(bridge_K), REFL(K_t))
    p_at_select = MP(spec_x, p_K_th)
    sel_t = mk_select(r_var, mk_eq(r_var, K_t))
    bridge_sel = BETA_CONV(mk_app(pred, sel_t))
    return EQ_MP(bridge_sel, p_at_select)


def _aty_for_select():
    """The schematic type variable used by SELECT_AX."""

    return aty


CtorRegistry = namedtuple(
    "CtorRegistry", ["ctors", "inj", "disjointness", "neq_empty", "empty_name"]
)


def _require_registry(registry, caller):
    if registry is None:
        raise ValueError(f"{caller}: registry is required")
    return registry


def _split_n_disj(tm):
    """Split a right-associated disjunction into its leaf list."""

    leaves = []
    while True:
        parts = dest_disj(tm)
        if parts is None:
            leaves.append(tm)
            return leaves
        leaves.append(parts[0])
        tm = parts[1]


def _spine_args(app):
    """For ``app = C a1 a2 ... ak`` return ``[a1, ..., ak]``."""

    args = []
    cur = app
    while not isinstance(cur, type(mk_const("0", []))):
        if hasattr(cur, "fun"):
            args.insert(0, cur.arg)
            cur = cur.fun
        else:
            break
    return args


def _disjunct_ctor_name(disj):
    """Identify the constructor head named in a body disjunct."""

    cur = disj
    while True:
        ex_pred = dest_exists(cur)
        if ex_pred is None:
            break
        cur = ex_pred.body
    eq_tm = dest_conj(cur)[0] if not is_eq(cur) else cur
    rhs = dest_eq(eq_tm)[1]
    head = rhs
    while not isinstance(head, type(mk_const("0", []))):
        if hasattr(head, "fun"):
            head = head.fun
        else:
            break
    if not hasattr(head, "name"):
        raise ValueError(f"_disjunct_ctor_name: cannot pin down constructor in {disj}")
    return head.name


def _ctor_neq_lemma(ctor_a_name, ctor_b_name, registry):
    """Look up a constructor disjointness theorem in ``registry``."""

    registry = _require_registry(registry, "_ctor_neq_lemma")
    if ctor_a_name == registry.empty_name:
        return ("rev", registry.neq_empty[ctor_b_name])
    if ctor_b_name == registry.empty_name:
        return ("fwd", registry.neq_empty[ctor_a_name])
    if (ctor_a_name, ctor_b_name) in registry.disjointness:
        return ("fwd", registry.disjointness[(ctor_a_name, ctor_b_name)])
    if (ctor_b_name, ctor_a_name) in registry.disjointness:
        return ("rev", registry.disjointness[(ctor_b_name, ctor_a_name)])
    raise ValueError(
        f"_ctor_neq_lemma: no disjointness for {ctor_a_name} vs {ctor_b_name}"
    )


def _spec_neq_at(neq_lemma_dir, ctor_a_args, ctor_b_args):
    """Specialise a disjointness theorem at concrete constructor args."""

    direction, lemma = neq_lemma_dir
    if direction == "fwd":
        return SPECL(ctor_a_args + ctor_b_args, lemma)
    swapped = SPECL(ctor_b_args + ctor_a_args, lemma)
    from tactics import NE_SYM

    return NE_SYM(swapped)


def _ctor_app(ctor_decl, args):
    """Build ``C a1 ... ak`` for a constructor registry entry."""

    return mk_app(mk_const(ctor_decl[0], []), *args)


def _disjunct_eq_F_via_neq(disj, neq_lemma_dir, target_args):
    """Prove ``|- disj = F`` for a non-matching constructor disjunct."""

    if is_eq(disj):
        neq_specd = _spec_neq_at(neq_lemma_dir, target_args, [])
        return SYM(EQF_INTRO(neq_specd))
    th = ASSUME(disj)
    while dest_exists(th._concl) is not None:
        th = CHOOSE_WITNESS(dest_exists(th._concl), th)
    head_eq_th = th if is_eq(th._concl) else CONJUNCT1(th)
    head_app = dest_eq(head_eq_th._concl)[1]
    other_args = _spine_args(head_app)
    neq_specd = _spec_neq_at(neq_lemma_dir, target_args, other_args)
    F_th = MP(NOT_ELIM(neq_specd), head_eq_th)
    rev = CONTR(disj, ASSUME(F))
    return DEDUCT_ANTISYM_RULE(rev, F_th)


def _disjunct_eq_match_unary(disj, target_app, target_arg, inj_lemma):
    """Matching unary disjunct: reduce to the target argument body."""

    ex_pred = dest_exists(disj)
    if ex_pred is None:
        raise ValueError("_disjunct_eq_match_unary: not existential")
    body = ex_pred.body
    conj = dest_conj(body)
    if conj is None:
        from tactics import EQT_INTRO

        rev = EXISTS(ex_pred, target_arg, REFL(target_app))
        return EQT_INTRO(rev)
    chosen = CHOOSE_WITNESS(ex_pred, ASSUME(disj))
    head_th = CONJUNCT1(chosen)
    rest_th = CONJUNCT2(chosen)
    sel_x = rand(head_th._concl)
    x_val = rand(sel_x)
    inj_at = SPECL([target_arg, x_val], inj_lemma)
    targ_eq_x = MP(inj_at, head_th)
    rest_at_target = REWRITE_RULE([SYM(targ_eq_x)], rest_th)
    rest_target_term = rest_at_target._concl
    body_th_at_target = CONJ(REFL(target_app), ASSUME(rest_target_term))
    rev = EXISTS(ex_pred, target_arg, body_th_at_target)
    return DEDUCT_ANTISYM_RULE(rev, rest_at_target)


def _disjunct_eq_match_binary(disj, target_app, target_args, inj_lemma):
    """Matching binary disjunct: reduce to the target argument body."""

    a_t, b_t = target_args
    out_a_pred = dest_exists(disj)
    in_b_pred = dest_exists(out_a_pred.body)
    chosen_a = CHOOSE_WITNESS(out_a_pred, ASSUME(disj))
    chosen_ab = CHOOSE_WITNESS(dest_exists(chosen_a._concl), chosen_a)
    head_th = CONJUNCT1(chosen_ab)
    rest_th = CONJUNCT2(chosen_ab)
    ctor_app = rand(head_th._concl)
    wb = rand(ctor_app)
    wa = rand(rator(ctor_app))
    pair = MP(SPECL([a_t, b_t, wa, wb], inj_lemma), head_th)
    eq_a = CONJUNCT1(pair)
    eq_b = CONJUNCT2(pair)
    rest_at_target = REWRITE_RULE([SYM(eq_a), SYM(eq_b)], rest_th)
    rest_target_term = rest_at_target._concl
    in_b_pred_at_a = mk_abs(
        in_b_pred.bvar,
        vsubst([(a_t, out_a_pred.bvar)])(in_b_pred.body),
    )
    inner_at_target = CONJ(REFL(target_app), ASSUME(rest_target_term))
    inner_th = EXISTS(in_b_pred_at_a, b_t, inner_at_target)
    outer_th = EXISTS(out_a_pred, a_t, inner_th)
    return DEDUCT_ANTISYM_RULE(outer_th, rest_at_target)


def derive_rec_eq(REC, target_ctor_name, var_names, *, registry=None):
    """Auto-derive a constructor recursion equation from a disjunctive REC."""

    from nat0 import nat0_ty

    registry = _require_registry(registry, "derive_rec_eq")
    if target_ctor_name not in registry.ctors:
        raise ValueError(f"derive_rec_eq: unknown ctor {target_ctor_name!r}")
    target_decl = registry.ctors[target_ctor_name]
    target_arity = len(target_decl[3])
    if len(var_names) != target_arity:
        raise ValueError(
            f"derive_rec_eq: {target_ctor_name} has arity {target_arity}, "
            f"got {len(var_names)} var names"
        )
    target_args = [Var(name, nat0_ty) for name in var_names]
    target_app = _ctor_app(target_decl, target_args)
    rec_at = SPEC(target_app, REC)
    disjuncts = _split_n_disj(rand(rec_at._concl))
    target_inj = registry.inj.get(target_ctor_name)
    per_eqs = []
    for disj in disjuncts:
        head_name = _disjunct_ctor_name(disj)
        if head_name == target_ctor_name:
            if target_arity == 1:
                eq = _disjunct_eq_match_unary(
                    disj, target_app, target_args[0], target_inj
                )
            else:
                eq = _disjunct_eq_match_binary(
                    disj, target_app, target_args, target_inj
                )
        else:
            neq_dir = _ctor_neq_lemma(target_ctor_name, head_name, registry)
            eq = _disjunct_eq_F_via_neq(disj, neq_dir, target_args)
        per_eqs.append(eq)
    return GENL(target_args, TRANS(rec_at, or_chain_collapse(per_eqs)))


def derive_rec_eq_pw(REC, target_ctor_name, var_names, *, registry=None):
    """Pointwise constructor recursion for function-valued recursion."""

    from nat0 import nat0_ty

    registry = _require_registry(registry, "derive_rec_eq_pw")
    if target_ctor_name not in registry.ctors:
        raise ValueError(f"derive_rec_eq_pw: unknown ctor {target_ctor_name!r}")
    target_decl = registry.ctors[target_ctor_name]
    target_arity = len(target_decl[3])
    if len(var_names) != target_arity:
        raise ValueError(
            f"derive_rec_eq_pw: {target_ctor_name} has arity {target_arity}, "
            f"got {len(var_names)} var names"
        )
    target_args = [Var(name, nat0_ty) for name in var_names]
    target_app = _ctor_app(target_decl, target_args)
    rec_at = SPEC(target_app, REC)
    v_bvar = rand(rec_at._concl).bvar
    rec_at_v = AP_THM(rec_at, v_bvar)
    rec_normalized = TRANS(rec_at_v, BETA_CONV(rand(rec_at_v._concl)))
    disjuncts = _split_n_disj(rand(rec_normalized._concl))
    target_inj = registry.inj.get(target_ctor_name)
    per_eqs = []
    for disj in disjuncts:
        head_name = _disjunct_ctor_name(disj)
        if head_name == target_ctor_name:
            if target_arity == 1:
                eq = _disjunct_eq_match_unary(
                    disj, target_app, target_args[0], target_inj
                )
            else:
                eq = _disjunct_eq_match_binary(
                    disj, target_app, target_args, target_inj
                )
        else:
            neq_dir = _ctor_neq_lemma(target_ctor_name, head_name, registry)
            eq = _disjunct_eq_F_via_neq(disj, neq_dir, target_args)
        per_eqs.append(eq)
    final = TRANS(rec_normalized, or_chain_collapse(per_eqs))
    return GENL(target_args + [v_bvar], final)


def _disjunct_eq_match_nullary(disj, target_app):
    r"""Matching nullary disjunct: ``target_app = target_app /\ R`` -> ``R``."""

    parts = dest_conj(disj)
    if parts is None:
        raise ValueError("_disjunct_eq_match_nullary: not a conjunction")
    _head_eq, rest = parts
    rest_th = CONJUNCT2(ASSUME(disj))
    disj_th = CONJ(REFL(target_app), ASSUME(rest))
    return DEDUCT_ANTISYM_RULE(disj_th, rest_th)


def derive_rec_eq_select(
    REC, target_ctor_name, var_names, extra_arg_vars, *, registry=None
):
    """Constructor recursion equation for SELECT-shaped recursion."""

    from nat0 import nat0_ty

    registry = _require_registry(registry, "derive_rec_eq_select")
    if target_ctor_name == registry.empty_name:
        if var_names:
            raise ValueError(
                f"derive_rec_eq_select: {registry.empty_name} is nullary; "
                "var_names must be empty"
            )
        target_arity = 0
        target_args = []
        target_app = mk_const(registry.empty_name, [])
    else:
        if target_ctor_name not in registry.ctors:
            raise ValueError(f"derive_rec_eq_select: unknown ctor {target_ctor_name!r}")
        target_decl = registry.ctors[target_ctor_name]
        target_arity = len(target_decl[3])
        if len(var_names) != target_arity:
            raise ValueError(
                f"derive_rec_eq_select: {target_ctor_name} has arity "
                f"{target_arity}, got {len(var_names)} var names"
            )
        target_args = [Var(name, nat0_ty) for name in var_names]
        target_app = _ctor_app(target_decl, target_args)

    cur = SPEC(target_app, REC)
    for arg in extra_arg_vars:
        cur_app = AP_THM(cur, arg)
        cur = TRANS(cur_app, BETA_CONV(rand(cur_app._concl)))
    select_term = rand(cur._concl)
    r_bvar = select_term.arg.bvar
    body_at = select_term.arg.body
    disjuncts = _split_n_disj(body_at)
    target_inj = registry.inj.get(target_ctor_name)
    per_eqs = []
    matched_K = None
    for disj in disjuncts:
        head_name = _disjunct_ctor_name(disj)
        if head_name == target_ctor_name:
            if target_arity == 0:
                eq = _disjunct_eq_match_nullary(disj, target_app)
            elif target_arity == 1:
                eq = _disjunct_eq_match_unary(
                    disj, target_app, target_args[0], target_inj
                )
            else:
                eq = _disjunct_eq_match_binary(
                    disj, target_app, target_args, target_inj
                )
            rhs = dest_eq(eq._concl)[1]
            if not is_eq(rhs):
                raise ValueError(
                    "derive_rec_eq_select: matched disjunct did not reduce "
                    f"to ``r = K``; got {rhs}"
                )
            r_lhs, K_t = dest_eq(rhs)
            if r_lhs != r_bvar:
                raise ValueError(
                    "derive_rec_eq_select: matched disjunct's eq is not "
                    f"``r = K`` (LHS = {r_lhs}, expected r = {r_bvar})."
                )
            matched_K = K_t
        else:
            neq_dir = _ctor_neq_lemma(target_ctor_name, head_name, registry)
            eq = _disjunct_eq_F_via_neq(disj, neq_dir, target_args)
        per_eqs.append(eq)
    if matched_K is None:
        raise ValueError(
            f"derive_rec_eq_select: no matching disjunct for {target_ctor_name}"
        )
    abs_body_eq = ABS(r_bvar, or_chain_collapse(per_eqs))
    sel_const = mk_const("@", [(r_bvar.ty, _aty_for_select())])
    select_to_K = TRANS(
        AP_TERM(sel_const, abs_body_eq), _select_collapse_eq(matched_K, r_bvar)
    )
    return GENL(target_args + list(extra_arg_vars), TRANS(cur, select_to_K))


def _conditional_body_eq(P_term, T_val, E_val, r_var, taking_then):
    r"""Collapse ``(P /\ r=T) \/ (~P /\ r=E)`` under ``P`` or ``~P``."""

    not_P = mk_not(P_term)
    eq_T = mk_eq(r_var, T_val)
    eq_E = mk_eq(r_var, E_val)
    left_conj = mk_and(P_term, eq_T)
    right_conj = mk_and(not_P, eq_E)
    body = mk_or(left_conj, right_conj)

    if taking_then:
        H = ASSUME(P_term)
        body_th = ASSUME(body)
        branch_l = DISCH(left_conj, CONJUNCT2(ASSUME(left_conj)))
        notP_th = CONJUNCT1(ASSUME(right_conj))
        F_th = MP(NOT_ELIM(notP_th), H)
        branch_r = DISCH(right_conj, CONTR(eq_T, F_th))
        forward = DISJ_CASES(body_th, branch_l, branch_r)
        reverse = DISJ1(CONJ(H, ASSUME(eq_T)), right_conj)
        return DEDUCT_ANTISYM_RULE(reverse, forward)

    H = ASSUME(not_P)
    body_th = ASSUME(body)
    P_th = CONJUNCT1(ASSUME(left_conj))
    F_th = MP(NOT_ELIM(H), P_th)
    branch_l = DISCH(left_conj, CONTR(eq_E, F_th))
    branch_r = DISCH(right_conj, CONJUNCT2(ASSUME(right_conj)))
    forward = DISJ_CASES(body_th, branch_l, branch_r)
    reverse = DISJ2(left_conj, CONJ(H, ASSUME(eq_E)))
    return DEDUCT_ANTISYM_RULE(reverse, forward)


def derive_rec_eq_select_cond(
    REC, target_ctor_name, var_names, extra_arg_vars, *, registry=None
):
    """SELECT-shaped constructor recursion for conditional matched bodies."""

    from nat0 import nat0_ty

    registry = _require_registry(registry, "derive_rec_eq_select_cond")
    if target_ctor_name not in registry.ctors:
        raise ValueError(
            f"derive_rec_eq_select_cond: unknown ctor {target_ctor_name!r}"
        )
    target_decl = registry.ctors[target_ctor_name]
    target_arity = len(target_decl[3])
    if len(var_names) != target_arity:
        raise ValueError(
            f"derive_rec_eq_select_cond: {target_ctor_name} has arity "
            f"{target_arity}, got {len(var_names)} var names"
        )
    target_args = [Var(name, nat0_ty) for name in var_names]
    target_app = _ctor_app(target_decl, target_args)
    cur = SPEC(target_app, REC)
    for arg in extra_arg_vars:
        cur_app = AP_THM(cur, arg)
        cur = TRANS(cur_app, BETA_CONV(rand(cur_app._concl)))
    select_term = rand(cur._concl)
    r_bvar = select_term.arg.bvar
    disjuncts = _split_n_disj(select_term.arg.body)
    target_inj = registry.inj.get(target_ctor_name)
    per_eqs = []
    matched_form = None
    for disj in disjuncts:
        head_name = _disjunct_ctor_name(disj)
        if head_name == target_ctor_name:
            if target_arity == 1:
                eq = _disjunct_eq_match_unary(
                    disj, target_app, target_args[0], target_inj
                )
            else:
                eq = _disjunct_eq_match_binary(
                    disj, target_app, target_args, target_inj
                )
            rhs = dest_eq(eq._concl)[1]
            disj_parts = dest_disj(rhs)
            if disj_parts is None:
                raise ValueError(
                    "derive_rec_eq_select_cond: matched disjunct's RHS is "
                    f"not a disjunction; got {rhs}"
                )
            left_parts = dest_conj(disj_parts[0])
            right_parts = dest_conj(disj_parts[1])
            if left_parts is None or right_parts is None:
                raise ValueError(
                    "derive_rec_eq_select_cond: matched RHS not "
                    "(P /\\ r = T) \\/ (~P /\\ r = E)"
                )
            P_t, eq_T = left_parts
            _not_P_t, eq_E = right_parts
            matched_form = (P_t, dest_eq(eq_T)[1], dest_eq(eq_E)[1])
        else:
            neq_dir = _ctor_neq_lemma(target_ctor_name, head_name, registry)
            eq = _disjunct_eq_F_via_neq(disj, neq_dir, target_args)
        per_eqs.append(eq)
    if matched_form is None:
        raise ValueError(
            f"derive_rec_eq_select_cond: no matching disjunct for {target_ctor_name}"
        )
    P_t, T_val, E_val = matched_form
    body_eq = or_chain_collapse(per_eqs)
    sel_const = mk_const("@", [(r_bvar.ty, _aty_for_select())])

    def _build_branch(taking_then, K_t, hyp_t):
        cond_eq = _conditional_body_eq(
            P_t, T_val, E_val, r_bvar, taking_then=taking_then
        )
        body_to_eqK = TRANS(body_eq, cond_eq)
        select_to_eqK = AP_TERM(sel_const, ABS(r_bvar, body_to_eqK))
        select_to_K = TRANS(select_to_eqK, _select_collapse_eq(K_t, r_bvar))
        return GENL(
            target_args + list(extra_arg_vars),
            DISCH(hyp_t, TRANS(cur, select_to_K)),
        )

    return (
        _build_branch(True, T_val, P_t),
        _build_branch(False, E_val, mk_not(P_t)),
    )


def define_nat0_binary_closure_predicate(
    pred_name,
    body_name,
    *,
    atoms,
    binary,
):
    r"""Define a nat0 recognizer closed under one binary constructor.

    ``atoms`` is a list of ``(surface_name, term)`` pairs. ``binary`` is
    ``(surface_name, const, size_left, size_right)``. The generated recognizer
    has body:

    ``n = atom1 \/ ... \/ (?a b. n = C a b /\\ f a /\\ f b)``.

    The function returns the helper body definition, monotonicity theorem,
    ``define_wf_lt`` definition/recursion theorem, the unfolded ``REC`` theorem,
    atom intro theorems, and the binary intro theorem.
    """

    from nat0 import nat0_ty
    from nat0_order import define_wf_lt

    pred_ty = parse_type("nat0 -> bool")
    body_ty = parse_type("(nat0 -> bool) -> nat0 -> bool")
    ctor_name, ctor_const, size_l, size_r = binary
    atom_disjuncts = [f"n = {atom_name}" for atom_name, _ in atoms]
    binary_disjunct = f"(?a b. n = {ctor_name} a b /\\ f a /\\ f b)"
    body_src = " \\/ ".join(atom_disjuncts + [binary_disjunct])

    body_def = define(
        body_name,
        body_ty,
        f"\\f:nat0->bool. \\n:nat0. {body_src}",
    )
    body_const = mk_const(body_name, [])

    @proof
    def mono(p):
        p.goal(
            f"!f g n. (!k. nat0_lt k n ==> f k = g k) "
            f"==> {body_name} f n = {body_name} g n",
            types={"f": pred_ty, "g": pred_ty, "n": nat0_ty, "k": nat0_ty},
        )
        p.fix("f g n")
        p.assume("h: !k. nat0_lt k n ==> f k = g k")
        h_th = p.fact("h")
        eqs = [REFL(p._parse(f"n = {atom_name}")) for atom_name, _ in atoms]
        eqs.append(mono_iff_binary_step(ctor_const, size_l, size_r, h_th))
        p.thus(f"{body_name} f n = {body_name} g n").by_unfold(
            or_chain_collapse(eqs), body_def
        )

    def_thm, rec_raw = define_wf_lt(pred_name, pred_ty, body_const, mono)
    pred_const = mk_const(pred_name, [])
    rec = unfold_rec_via_body_def(rec_raw, body_def)

    body_at = {
        atom_name: " \\/ ".join(
            [f"{atom_name} = {other_name}" for other_name, _ in atoms]
            + [f"(?a b. {atom_name} = {ctor_name} a b /\\ {pred_name} a /\\ {pred_name} b)"]
        )
        for atom_name, _ in atoms
    }

    atom_intros = []
    for atom_name, atom_term in atoms:

        @proof
        def atom_intro(p, atom_name=atom_name, atom_term=atom_term):
            p.goal(f"{pred_name} {atom_name}")
            p.have(f"h_self: {atom_name} = {atom_name}").by_thm(REFL(atom_term))
            p.have(f"rhs: {body_at[atom_name]}").by_disj("h_self")
            p.thus(f"{pred_name} {atom_name}").by_eq_mp(SPEC(atom_term, rec), "rhs")

        atom_intros.append(atom_intro)

    @proof
    def binary_intro(p):
        p.goal(
            f"!a b. {pred_name} a /\\ {pred_name} b ==> "
            f"{pred_name} ({ctor_name} a b)"
        )
        p.fix("a b")
        p.assume(f"(ha, hb): {pred_name} a /\\ {pred_name} b")
        p.have(
            f"inner: ?x y. {ctor_name} a b = {ctor_name} x y /\\ "
            f"{pred_name} x /\\ {pred_name} y"
        ).by_exists(["a", "b"], "ha", "hb")
        ctor_ab = f"{ctor_name} a b"
        rhs = " \\/ ".join(
            [f"{ctor_ab} = {atom_name}" for atom_name, _ in atoms]
            + [
                f"(?x y. {ctor_ab} = {ctor_name} x y /\\ "
                f"{pred_name} x /\\ {pred_name} y)"
            ]
        )
        p.have(f"rhs: {rhs}").by_disj("inner")
        spec = SPEC(mk_app(ctor_const, p._parse("a"), p._parse("b")), rec)
        p.thus(f"{pred_name} ({ctor_name} a b)").by_eq_mp(spec, "rhs")

    return Nat0BinaryClosurePredicate(
        pred_name,
        pred_const,
        body_def,
        body_const,
        mono,
        def_thm,
        rec_raw,
        rec,
        atom_intros,
        binary_intro,
    )
