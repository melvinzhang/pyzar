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

from fusion import Var, ASSUME, EQ_MP, DEDUCT_ANTISYM_RULE
from fusion import mk_type, new_basic_type_definition
from basics import mk_const, mk_abs, mk_app, mk_eq, dest_eq, rator, rand
from parser import add_const, add_type, define, parse_type
from axioms import mk_and, mk_exists, dest_exists, dest_forall, dest_imp
from proof import proof, define_with_at
from tactics import (
    SPEC,
    SYM,
    MP,
    CHOOSE_WITNESS,
    CONJ,
    CONJUNCT1,
    CONJUNCT2,
    EXISTS,
    REWRITE_RULE,
    REWRITE_CONV,
    TRANS,
    BETA_NORM,
    REFL,
    GEN,
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
