"""Hereditarily finite sets via Ackermann's bit-encoding.

SKETCH ONLY -- this file lays out the construction; the proofs are
stubbed with strategy comments rather than executed. Scope is set by
the immediate downstream consumer ``godel_first.py``: we build only as
much HF as it needs (encoding for the syntax of HF and its model).
The general ZF constructors (Pow, Repl, Sep) are noted but deferred to
a follow-up file -- ``godel_first.py`` does not call them.

Stage 1 (bit operations on ``nat0``) is now LIVE in ``bits.py``: see
the symbol list below. Everything else in this file is a sketch.

Axiomatic cost: zero. HOL + ``nat0`` + the bit-extensionality lemma
already proved in ``bits.py`` is the entire substrate.

------------------------------------------------------------------
The idea (Ackermann 1937)
------------------------------------------------------------------

A natural number ``n`` *is* a hereditarily finite set: write ``n`` in
binary, read off the positions of the 1-bits, and recursively decode
each position as another HF set. So

    0       = {}
    1       = {0}              = {{}}
    2       = {1}              = {{{}}}
    3       = {0, 1}           = {{}, {{}}}
    4       = {2}              = {{{{}}}}
    5       = {0, 2}           = {{}, {{{}}}}
    ...

The recipe collapses to a single arithmetical predicate:

    In x y   <=>   bit x of y is 1.

The encoding is a bijection between ``nat0`` and HF, and every HF
operation we need below becomes an arithmetic operation on ``nat0``.

------------------------------------------------------------------
Why no nominal type
------------------------------------------------------------------

The original sketch wrapped HF in a one-line subtype
(``new_basic_type_definition`` over ``\\n. T``) to keep ``+`` and
``*`` from accidentally typechecking on HF sets. For
``godel_first.py`` we never *want* to do nat0-arithmetic on a
"formula encoding" by accident -- but the formal cost of a subtype
is two coercions (``rep_hf``, ``abs_hf``) threaded through every
lemma. Drop the subtype: write ``hf_ty := nat0_ty`` as a plain alias.
If this turns out to bite us in ``godel_first.py``, reinstate the
subtype later -- it is a syntactic refactor, not a proof rewrite.
"""

# Optional follow-ups (each strictly downstream of this file):
#   * ``hf_zf.py``     -- Pow, Repl, Sep, refutation of Infinity.
#                         Needed only if someone wants Landau Saetze
#                         1-150 over the formalised ZF surface.
#                         ~250 lines.
#   * ``hf_arith.py``  -- ``rep`` on the vN image as an actual nat0
#                         function (HOL-level, not HF-internal),
#                         giving the PA <-> ZF-Inf transport
#                         concretely. ~150 lines. Strictly nice-to-
#                         have; godel_first.py does not call it.


# ---------------------------------------------------------------------------
# Stage 2 -- HF and In.
# ---------------------------------------------------------------------------
#
#   hf_ty   := nat0_ty                            (alias; no subtype)
#   In x y :<=> bit x y                           (HOL bool)
#
# That's it. ``In`` is just ``bit`` under a friendlier name.
#
# Lemmas proved below (all by trivial unfold to the corresponding
# bit-level theorem in bits.py):
#
#   IN_AT  : |- !x y. In x y = bit x y
#     Pointwise unfolding of IN_DEF; the workhorse rewrite that lets
#     downstream proofs hop between ``In`` and ``bit`` freely.
#
#   IN_ZERO : |- !x. In x 0 = F
#     From BIT_AT_ZERO. Stated against ``0:nat0`` rather than
#     ``Empty`` because ``Empty`` is not introduced until Stage 3.
#     The ``Empty`` form (NOT_IN_EMPTY) is restated there as a one-
#     line rewrite via EMPTY_DEF.
#
#   IN_LT : |- !y x. In x y ==> nat0_lt x y
#     The membership-decreases-numeric-value fact, from BIT_LT. This
#     is the half of "Foundation as a derived rule" that godel_first.py
#     would actually use if it ever needed it; the full Foundation
#     statement is not reified -- see the Stage 3 deferral list.
#
#   IN_EXT : |- !a b. (!x. In x a = In x b) ==> a = b
#     Extensionality, from BIT_EXTENSIONALITY: lift the inner equality
#     to the bit level under the universal quantifier and apply.
#
# No proof work beyond definitional unfolding. ~50 lines including
# the IN_AT scaffolding.

from fusion import Var
from basics import mk_abs, mk_app, mk_const, rand
from parser import define, parse_type
from nat0 import (
    nat0_ty,
    ZERO,
    AXIOM_3_0,
    AXIOM_4_0,
    define_unary_0,
    define_recursive_0,
    mk_suc0,
)
from bits import BIT_AT_ZERO, BIT_LT, BIT_EXTENSIONALITY
from nat0_order import nat0_lt, NAT0_LT_ASYM  # noqa: F401  -- parser alias
from proof import proof


# ``hf`` is a synonym for ``nat0`` -- no nominal subtype.
hf_ty = nat0_ty


# ---------------------------------------------------------------------------
# Definition: ``In x y`` :<=> ``bit x y``.
# ---------------------------------------------------------------------------

IN_DEF = define(
    "In",
    parse_type("nat0 -> nat0 -> bool"),
    "\\x:nat0. \\y:nat0. bit x y",
)
In = mk_const("In", [])


_x_n0 = Var("x", nat0_ty)
_y_n0 = Var("y", nat0_ty)


# Pointwise unfolding:  |- !x y. In x y = bit x y.
def _prove_in_at():
    from fusion import REFL  # noqa: F401
    from tactics import AP_THM, BETA_CONV, TRANS, GENL

    th_x = AP_THM(IN_DEF, _x_n0)  # |- In x = (\x. \y. bit x y) x
    th_x_eq = TRANS(th_x, BETA_CONV(rand(th_x._concl)))
    th_xy = AP_THM(th_x_eq, _y_n0)  # |- In x y = (\y. bit x y) y
    return GENL([_x_n0, _y_n0], TRANS(th_xy, BETA_CONV(rand(th_xy._concl))))


IN_AT = _prove_in_at()


# ---------------------------------------------------------------------------
# Lemma:  |- !x. In x 0 = F.
# Direct unfolding to BIT_AT_ZERO.
# ---------------------------------------------------------------------------


@proof
def IN_ZERO(p):
    p.goal("!x. In x 0 = F")
    p.fix("x")
    p.thus("In x 0 = F").by_rewrite([IN_AT, BIT_AT_ZERO])


# ---------------------------------------------------------------------------
# Lemma:  |- !y x. In x y ==> nat0_lt x y.   (foundation core.)
# Mirror of BIT_LT under the In-defunfold.
# ---------------------------------------------------------------------------


@proof
def IN_LT(p):
    p.goal("!y x. In x y ==> nat0_lt x y")
    p.fix("y x")
    p.assume("h: In x y")
    p.have("hb: bit x y").by_rewrite_of("h", [IN_AT])
    p.thus("nat0_lt x y").by(BIT_LT, "y", "x", "hb")


# ---------------------------------------------------------------------------
# Lemma:  |- !a b. (!x. In x a = In x b) ==> a = b.   (extensionality.)
# Mirror of BIT_EXTENSIONALITY under the In-defunfold (lifted under the
# inner forall).
# ---------------------------------------------------------------------------


@proof
def IN_EXT(p):
    p.goal("!a b. (!x. In x a = In x b) ==> a = b")
    p.fix("a b")
    p.assume("h: !x. In x a = In x b")
    with p.have("hb: !i. bit i a = bit i b").proof():
        p.fix("i")
        p.have("hi: In i a = In i b").by("h", "i")
        p.thus("bit i a = bit i b").by_rewrite_of("hi", [IN_AT])
    p.thus("a = b").by(BIT_EXTENSIONALITY, "a", "b", "hb")


# ---------------------------------------------------------------------------
# Stage 3 -- HF constructors needed by godel_first.py.
#
# Scope is set by what godel_first.py Stage 1 actually consumes for
# encoding HF syntax as HF trees: Empty, Insert, Singleton, Pair, and
# the ordered Kuratowski pair Pair_ord (for (index, value) tuple entries).
# Stage 4's HF-model construction sits on top of Insert (vN_succ x =
# Insert x x) and does not need Union, Pow, Repl, Sep, or a derived
# Foundation rule. Pow / Repl / Sep are still deferred:
#
#   * Union  -- now defined further below (Stage 3 cont.) as a binary
#               bit-OR ``Union a b`` via well-founded recursion on
#               HALF a; the membership characterisation is IN_UNION.
#               Stage 4 still uses ``Insert x x`` for vN_succ; Union
#               is required by downstream code (hf_repr.py) that needs
#               to combine HF-set traces in the substitute representability
#               proof.
#   * Pow, Repl, Sep  -- general ZF constructors; defer to a future
#               ``hf_zf.py`` if a consumer wants full ZF surface.
#   * Foundation as a derived rule -- a one-liner via BIT_LT + nat0
#               well-ordering, but unused by godel_first.py (the
#               HF-consistency argument needs the positive fact that
#               HF has a HOL-level model, not Foundation).
#   * Refutation of Infinity -- nice corollary, also unused here.
#
# What is proved below:
#
#   EMPTY      -- defn ``Empty := 0``;
#                 NOT_IN_EMPTY: |- !x. ~In x Empty
#                   (trivial unfold to BIT_AT_ZERO + EQF_ELIM).
#
#   INSERT     -- defn ``Insert i s := set_bit i s``;
#                 IN_INSERT_SAME: |- !i s. In i (Insert i s) = T
#                   (BIT_AT_SET_BIT_SAME);
#                 IN_INSERT_DIFF: |- !i j s. ~(i = j) ==>
#                                            In j (Insert i s) = In j s
#                   (BIT_AT_SET_BIT_DIFF).
#                 Both are direct renames of the bit-level lemmas.
#
#   SINGLETON  -- defn ``Singleton x := pow2 x`` (= Insert x Empty);
#                 IN_SINGLETON: |- !x y. In y (Singleton x) = (y = x)
#                   case-split on y = x via EXCLUDED_MIDDLE,
#                   BIT_AT_POW2_SAME / BIT_AT_POW2_DIFF on each branch.
#
#   PAIR       -- defn ``Pair x y := Insert x (Singleton y)``;
#                 IN_PAIR: |- !a b z. In z (Pair a b) = (z = a \/ z = b)
#                   case-split on z = a; the diff branch reduces to
#                   IN_SINGLETON on b, and we discharge the disjunction
#                   shape on each side.
#
#   PAIR_ORD   -- defn ``Pair_ord x y := Pair (Singleton x) (Pair x y)``
#                 (Kuratowski {{x}, {x, y}});
#                 IN_PAIR_ORD: |- !a b z. In z (Pair_ord a b) =
#                                 (z = Singleton a \/ z = Pair a b)
#                   one rewrite via PAIR_ORD_AT + IN_PAIR.
#
#                 The ordered-pair injectivity theorem
#                   |- Pair_ord a b = Pair_ord c d <=> (a = c /\ b = d)
# ---------------------------------------------------------------------------

from bits import (  # noqa: E402 -- needs nat0_lt parser alias registered above
    BIT_AT_SET_BIT_SAME,
    BIT_AT_SET_BIT_DIFF,
    BIT_AT_POW2_SAME,
    BIT_AT_POW2_DIFF,
    POW2_AS_SET_BIT,
    LOW_BIT_SET_BIT_NEW,
    SET_BIT_GT_NEW,
    POW2_LT_MONO,
)
from nat0_order import NAT0_LT_TRANS, NAT0_LT_NOT_REFL  # noqa: E402
from tactics import REFL, DISJ1  # noqa: E402


_i_n0 = Var("i", nat0_ty)
_j_n0 = Var("j", nat0_ty)
_s_n0 = Var("s", nat0_ty)
_a_n0 = Var("a", nat0_ty)
_b_n0 = Var("b", nat0_ty)


# ---------------------------------------------------------------------------
# Empty := 0.
# ---------------------------------------------------------------------------

EMPTY_DEF = define("Empty", parse_type("nat0"), ZERO)
Empty = mk_const("Empty", [])


# Lemma: |- !x. ~In x Empty.   (Trivial unfold to BIT_AT_ZERO + EQF_ELIM.)
@proof
def NOT_IN_EMPTY(p):
    from tactics import EQF_ELIM

    p.goal("!x. ~In x Empty")
    p.fix("x")
    p.have("h: In x Empty = F").by_rewrite([EMPTY_DEF, IN_AT, BIT_AT_ZERO])
    p.thus("~In x Empty").by_thm(EQF_ELIM(p.fact("h")))


# ---------------------------------------------------------------------------
# Insert i s := set_bit i s.
# ---------------------------------------------------------------------------

INSERT_DEF = define(
    "Insert",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\i:nat0. \\s:nat0. set_bit i s",
)
Insert = mk_const("Insert", [])


# Pointwise: |- !i s. Insert i s = set_bit i s.
def _prove_insert_at():
    from tactics import AP_THM, BETA_CONV, TRANS, GENL

    th_i = AP_THM(INSERT_DEF, _i_n0)
    th_i_eq = TRANS(th_i, BETA_CONV(rand(th_i._concl)))
    th_is = AP_THM(th_i_eq, _s_n0)
    return GENL([_i_n0, _s_n0], TRANS(th_is, BETA_CONV(rand(th_is._concl))))


INSERT_AT = _prove_insert_at()


# Lemma: |- !i s. In i (Insert i s) = T.   (Mirror of BIT_AT_SET_BIT_SAME.)
@proof
def IN_INSERT_SAME(p):
    p.goal("!i s. In i (Insert i s) = T")
    p.fix("i s")
    p.thus("In i (Insert i s) = T").by_rewrite([IN_AT, INSERT_AT, BIT_AT_SET_BIT_SAME])


# Lemma: |- !i j s. ~(i = j) ==> In j (Insert i s) = In j s.
@proof
def IN_INSERT_DIFF(p):
    p.goal("!i j s. ~(i = j) ==> In j (Insert i s) = In j s")
    p.fix("i j s")
    p.assume("h: ~(i = j)")
    p.have("hb: bit j (set_bit i s) = bit j s").by(
        BIT_AT_SET_BIT_DIFF, "i", "j", "s", "h"
    )
    p.thus("In j (Insert i s) = In j s").by_rewrite_of("hb", [IN_AT, INSERT_AT])


# ---------------------------------------------------------------------------
# Singleton x := pow2 x   ( = Insert x Empty ).
# ---------------------------------------------------------------------------

SINGLETON_DEF = define(
    "Singleton",
    parse_type("nat0 -> nat0"),
    "\\x:nat0. pow2 x",
)
Singleton = mk_const("Singleton", [])


# Pointwise: |- !x. Singleton x = pow2 x.
def _prove_singleton_at():
    from tactics import AP_THM, BETA_CONV, TRANS, GEN

    th_x = AP_THM(SINGLETON_DEF, _x_n0)
    return GEN(_x_n0, TRANS(th_x, BETA_CONV(rand(th_x._concl))))


SINGLETON_AT = _prove_singleton_at()


# Lemma: |- !x. Singleton x = Insert x Empty.
#
# Bridges the pow2-flavoured ``Singleton`` to the bit-flavoured
# ``Insert``. Used by ``hf_repr.QUOTE_HF_AT_SINGLETON`` (and Stage 3
# representability stubs) to fold ``Singleton x`` into a one-step
# ``Insert``-tower over ``Empty``.
@proof
def SINGLETON_AS_INSERT(p):
    """|- !x. Singleton x = Insert x Empty."""
    p.goal("!x. Singleton x = Insert x Empty")
    p.fix("x")
    p.thus("Singleton x = Insert x Empty").by_rewrite(
        [SINGLETON_AT, POW2_AS_SET_BIT, EMPTY_DEF, INSERT_AT]
    )


# Lemma: |- !i. low_bit (Singleton i) = i.
#
# Singleton i = pow2 i = set_bit i 0; the s = 0 disjunct of
# LOW_BIT_SET_BIT_NEW's precondition discharges trivially, leaving
# low_bit (set_bit i 0) = i.
@proof
def LOW_BIT_SINGLETON(p):
    """|- !i. low_bit (Singleton i) = i."""
    from tactics import SYM

    p.goal("!i. low_bit (Singleton i) = i")
    p.fix("i")
    with p.have("h_pre: 0 = 0 \\/ nat0_lt i (low_bit 0)").proof():
        p.disj(REFL(ZERO))
    p.have("lb_sb: low_bit (set_bit i 0) = i").by(
        LOW_BIT_SET_BIT_NEW, "i", "0", "h_pre"
    )
    p.thus("low_bit (Singleton i) = i").by_rewrite_of(
        "lb_sb", [SINGLETON_AT, POW2_AS_SET_BIT]
    )


# Lemma: |- !x y. In y (Singleton x) = (y = x).
# Case-split on y = x; in each case both sides reduce to the same boolean.
@proof
def IN_SINGLETON(p):
    from classical import EXCLUDED_MIDDLE
    from tactics import EQT_INTRO, EQF_INTRO

    p.goal("!x y. In y (Singleton x) = (y = x)")
    p.fix("x y")
    with p.cases_on(EXCLUDED_MIDDLE, "y = x"):
        with p.case("hyx: y = x"):
            p.have("h_lhs: In y (Singleton x) = T").by_rewrite(
                [IN_AT, SINGLETON_AT, "hyx", BIT_AT_POW2_SAME]
            )
            p.have("h_rhs: (y = x) = T").by_thm(EQT_INTRO(p.fact("hyx")))
            p.thus("In y (Singleton x) = (y = x)").by_rewrite(["h_lhs", "h_rhs"])
        with p.case("hnyx: ~(y = x)"):
            p.have("hb: bit y (pow2 x) = F").by(BIT_AT_POW2_DIFF, "x", "y", "hnyx")
            p.have("h_lhs: In y (Singleton x) = F").by_rewrite_of(
                "hb", [IN_AT, SINGLETON_AT]
            )
            p.have("h_rhs: (y = x) = F").by_thm(EQF_INTRO(p.fact("hnyx")))
            p.thus("In y (Singleton x) = (y = x)").by_rewrite(["h_lhs", "h_rhs"])


# ---------------------------------------------------------------------------
# Pair x y := Insert x (Singleton y).   (Unordered pair {x, y}.)
# ---------------------------------------------------------------------------

PAIR_DEF = define(
    "Pair",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\x:nat0. \\y:nat0. Insert x (Singleton y)",
)
Pair = mk_const("Pair", [])


# Pointwise: |- !x y. Pair x y = Insert x (Singleton y).
def _prove_pair_at():
    from tactics import AP_THM, BETA_CONV, TRANS, GENL

    th_x = AP_THM(PAIR_DEF, _x_n0)
    th_x_eq = TRANS(th_x, BETA_CONV(rand(th_x._concl)))
    th_xy = AP_THM(th_x_eq, _y_n0)
    return GENL([_x_n0, _y_n0], TRANS(th_xy, BETA_CONV(rand(th_xy._concl))))


PAIR_AT = _prove_pair_at()


# Lemma: |- !a b z. In z (Pair a b) = (z = a \/ z = b).
# Case-split on z = a; in the ``z = a`` branch both sides are T, in the
# ``~(z = a)`` branch both sides equal (z = b).
@proof
def IN_PAIR(p):
    from classical import EXCLUDED_MIDDLE
    from tactics import EQT_INTRO, SYM

    p.goal("!a b z. In z (Pair a b) = (z = a \\/ z = b)")
    p.fix("a b z")
    with p.cases_on(EXCLUDED_MIDDLE, "z = a"):
        with p.case("hza: z = a"):
            p.have("h_lhs: In z (Pair a b) = T").by_rewrite(
                [PAIR_AT, IN_AT, INSERT_AT, "hza", BIT_AT_SET_BIT_SAME]
            )
            p.have("h_disj: z = a \\/ z = b").by_disj("hza")
            p.have("h_rhs: (z = a \\/ z = b) = T").by_thm(EQT_INTRO(p.fact("h_disj")))
            p.thus("In z (Pair a b) = (z = a \\/ z = b)").by_rewrite(["h_lhs", "h_rhs"])
        with p.case("hnza: ~(z = a)"):
            # IN_INSERT_DIFF needs ~(a = z); flip ~(z = a).
            with p.have("h_az: ~(a = z)").proof():
                with p.suppose("haz: a = z"):
                    p.have("hza2: z = a").by_thm(SYM(p.fact("haz")))
                    p.absurd().by_conj("hnza", "hza2")
            p.have("h_diff: In z (Insert a (Singleton b)) = In z (Singleton b)").by(
                IN_INSERT_DIFF, "a", "z", "Singleton b", "h_az"
            )
            p.have("h_sing: In z (Singleton b) = (z = b)").by(IN_SINGLETON, "b", "z")
            p.have("h_lhs: In z (Pair a b) = (z = b)").by_rewrite(
                [PAIR_AT, "h_diff", "h_sing"]
            )
            # RHS simplifies to (z = b) under ~(z = a) -- by_iff both ways.
            with p.have("h_rhs: (z = a \\/ z = b) = (z = b)").proof():
                with p.have("fwd: (z = a \\/ z = b) ==> (z = b)").proof():
                    p.assume("hd: z = a \\/ z = b")
                    with p.cases_on("hd"):
                        with p.case("hza2: z = a"):
                            p.absurd().by_conj("hnza", "hza2")
                        with p.case("hzb: z = b"):
                            p.thus("z = b").by_thm(p.fact("hzb"))
                with p.have("rev: (z = b) ==> (z = a \\/ z = b)").proof():
                    p.assume("hzb: z = b")
                    p.thus("z = a \\/ z = b").by_disj("hzb")
                p.thus("(z = a \\/ z = b) = (z = b)").by_iff("fwd", "rev")
            p.thus("In z (Pair a b) = (z = a \\/ z = b)").by_rewrite(["h_lhs", "h_rhs"])


# Lemma: |- !x y. nat0_lt x y ==> nat0_lt (Singleton x) (Pair x y).
#
# Bit-arithmetic helper for ``hf_repr.QUOTE_HF_AT_PAIR_ORD``. Composes
# POW2_LT_MONO (nat0_lt x y ==> nat0_lt (pow2 x) (pow2 y)) with
# SET_BIT_GT_NEW at the outer set_bit x (pow2 y) layer. Specifically:
#
#   * Pair x y = Insert x (Singleton y) = set_bit x (pow2 y)
#     [PAIR_AT, INSERT_AT, SINGLETON_AT].
#   * bit x (pow2 y) = F under x != y (BIT_AT_POW2_DIFF; ~(x = y) follows
#     from nat0_lt x y via NAT0_LT_NOT_REFL).
#   * SET_BIT_GT_NEW: nat0_lt (pow2 y) (set_bit x (pow2 y)) =
#     nat0_lt (pow2 y) (Pair x y).
#   * POW2_LT_MONO: nat0_lt (pow2 x) (pow2 y) under nat0_lt x y.
#   * NAT0_LT_TRANS chains the two halves.
@proof
def SINGLETON_LT_PAIR(p):
    """|- !x y. nat0_lt x y ==> nat0_lt (Singleton x) (Pair x y)."""
    from tactics import EQF_INTRO, SYM, EQF_ELIM

    p.goal("!x y. nat0_lt x y ==> nat0_lt (Singleton x) (Pair x y)")
    p.fix("x y")
    p.assume("hxy: nat0_lt x y")
    # x != y (asymmetry / irreflexivity of nat0_lt).
    with p.have("hne: ~(x = y)").proof():
        with p.suppose("h_eq: x = y"):
            p.have("h_lt_self: nat0_lt y y").by_rewrite_of(
                "hxy", ["h_eq"]
            )
            p.have("h_not_lt: ~(nat0_lt y y)").by(NAT0_LT_NOT_REFL, "y")
            p.absurd().by_conj("h_not_lt", "h_lt_self")
    # bit x (pow2 y) = F.
    p.have("h_bit_F: bit x (pow2 y) = F").by(
        BIT_AT_POW2_DIFF, "y", "x", "hne"
    )
    p.have("h_not_bit: ~(bit x (pow2 y))").by_thm(EQF_ELIM(p.fact("h_bit_F")))
    # Pair x y = set_bit x (pow2 y).
    p.have(
        "h_pair_eq: Pair x y = set_bit x (pow2 y)"
    ).by_rewrite([PAIR_AT, INSERT_AT, SINGLETON_AT])
    # SET_BIT_GT_NEW: nat0_lt (pow2 y) (set_bit x (pow2 y)).
    p.have(
        "h_p2y_lt_pair: nat0_lt (pow2 y) (set_bit x (pow2 y))"
    ).by(SET_BIT_GT_NEW, "x", "pow2 y", "h_not_bit")
    # POW2_LT_MONO: nat0_lt (pow2 x) (pow2 y).
    p.have(
        "h_p2x_lt_p2y: nat0_lt (pow2 x) (pow2 y)"
    ).by(POW2_LT_MONO, "x", "y", "hxy")
    # Chain.
    p.have(
        "h_p2x_lt_pair: nat0_lt (pow2 x) (set_bit x (pow2 y))"
    ).by(
        NAT0_LT_TRANS,
        "pow2 x",
        "pow2 y",
        "set_bit x (pow2 y)",
        "h_p2x_lt_p2y",
        "h_p2y_lt_pair",
    )
    p.thus(
        "nat0_lt (Singleton x) (Pair x y)"
    ).by_rewrite_of(
        "h_p2x_lt_pair", [SINGLETON_AT, p.fact("h_pair_eq")]
    )


# ---------------------------------------------------------------------------
# Pair_ord x y := Pair (Singleton x) (Pair x y).   (Kuratowski ordered pair
# {{x}, {x, y}}.)
# ---------------------------------------------------------------------------

PAIR_ORD_DEF = define(
    "Pair_ord",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\x:nat0. \\y:nat0. Pair (Singleton x) (Pair x y)",
)
Pair_ord = mk_const("Pair_ord", [])


# Pointwise: |- !x y. Pair_ord x y = Pair (Singleton x) (Pair x y).
def _prove_pair_ord_at():
    from tactics import AP_THM, BETA_CONV, TRANS, GENL

    th_x = AP_THM(PAIR_ORD_DEF, _x_n0)
    th_x_eq = TRANS(th_x, BETA_CONV(rand(th_x._concl)))
    th_xy = AP_THM(th_x_eq, _y_n0)
    return GENL([_x_n0, _y_n0], TRANS(th_xy, BETA_CONV(rand(th_xy._concl))))


PAIR_ORD_AT = _prove_pair_ord_at()


# Membership characterisation:
#   |- !a b z. In z (Pair_ord a b) = (z = Singleton a \/ z = Pair a b).
# Direct rewrite via PAIR_ORD_AT + IN_PAIR.
@proof
def IN_PAIR_ORD(p):
    p.goal("!a b z. In z (Pair_ord a b) = (z = Singleton a \\/ z = Pair a b)")
    p.fix("a b z")
    p.have(
        "h: In z (Pair (Singleton a) (Pair a b)) = (z = Singleton a \\/ z = Pair a b)"
    ).by(IN_PAIR, "Singleton a", "Pair a b", "z")
    p.thus("In z (Pair_ord a b) = (z = Singleton a \\/ z = Pair a b)").by_rewrite_of(
        "h", [PAIR_ORD_AT]
    )


# ---------------------------------------------------------------------------
# Stage 3 (cont.) -- structural lemmas for ``Pair_ord``.
#
# These two lemmas drive the encoding work in ``hf_syntax.py``:
#
#   PAIR_ORD_INJ   -- Kuratowski ordered-pair injectivity, the basis
#                     for HF-constructor injectivity and disjointness.
#   NAT0_LT_PAIR_ORD_L / _R -- size lemmas that say each component of
#                     a ``Pair_ord`` lies strictly below it under
#                     ``nat0_lt``.  These chain through a constructor's
#                     pair-of-pairs encoding via ``NAT0_LT_TRANS`` to
#                     give "each argument is strictly smaller than the
#                     constructed term", the side condition required by
#                     ``define_wf_lt``.
#
# Helper lemmas used by ``PAIR_ORD_INJ`` (and reusable in their own
# right):
#
#   SINGLETON_INJ     :  |- !a b. Singleton a = Singleton b ==> a = b.
#   SINGLETON_EQ_PAIR :  |- !x a b. Singleton x = Pair a b
#                                     ==> (x = a /\ x = b).
# ---------------------------------------------------------------------------


# Lemma:  |- !a b. Singleton a = Singleton b ==> a = b.
@proof
def SINGLETON_INJ(p):
    from fusion import REFL
    from tactics import SYM

    p.goal("!a b. Singleton a = Singleton b ==> a = b")
    p.fix("a b")
    p.assume("h: Singleton a = Singleton b")
    # In a (Singleton a) = (a = a), and a = a holds, so In a (Singleton a).
    p.have("e_aa: In a (Singleton a) = (a = a)").by(IN_SINGLETON, "a", "a")
    p.have("haa: a = a").by_thm(REFL(p._parse("a")))
    p.have("h_in_a: In a (Singleton a)").by_eq_mp(SYM(p.fact("e_aa")), "haa")
    # Transport via h.
    p.have("h_in_b: In a (Singleton b)").by_rewrite_of("h_in_a", ["h"])
    # In a (Singleton b) = (a = b); EQ_MP yields a = b.
    p.have("e_ab: In a (Singleton b) = (a = b)").by(IN_SINGLETON, "b", "a")
    p.thus("a = b").by_eq_mp(p.fact("e_ab"), "h_in_b")


# Lemma:  |- !x a b. Singleton x = Pair a b ==> (x = a /\ x = b).
@proof
def SINGLETON_EQ_PAIR(p):
    from fusion import REFL
    from tactics import SYM, CONJ

    p.goal("!x a b. Singleton x = Pair a b ==> (x = a /\\ x = b)")
    p.fix("x a b")
    p.assume("h: Singleton x = Pair a b")
    p.have("h_sym: Pair a b = Singleton x").by_thm(SYM(p.fact("h")))

    # Show x = a: a in Pair a b (left), so a in Singleton x, so a = x.
    p.have("haa: a = a").by_thm(REFL(p._parse("a")))
    p.have("hd_a: a = a \\/ a = b").by_disj("haa")
    p.have("e_a: In a (Pair a b) = (a = a \\/ a = b)").by(IN_PAIR, "a", "b", "a")
    p.have("h_a_pair: In a (Pair a b)").by_eq_mp(SYM(p.fact("e_a")), "hd_a")
    p.have("h_a_sing: In a (Singleton x)").by_rewrite_of("h_a_pair", ["h_sym"])
    p.have("e_xa: In a (Singleton x) = (a = x)").by(IN_SINGLETON, "x", "a")
    p.have("h_a_eq_x: a = x").by_eq_mp(p.fact("e_xa"), "h_a_sing")
    p.have("hxa: x = a").by_thm(SYM(p.fact("h_a_eq_x")))

    # Show x = b: same shape on the b side.
    p.have("hbb: b = b").by_thm(REFL(p._parse("b")))
    p.have("hd_b: b = a \\/ b = b").by_disj("hbb")
    p.have("e_b: In b (Pair a b) = (b = a \\/ b = b)").by(IN_PAIR, "a", "b", "b")
    p.have("h_b_pair: In b (Pair a b)").by_eq_mp(SYM(p.fact("e_b")), "hd_b")
    p.have("h_b_sing: In b (Singleton x)").by_rewrite_of("h_b_pair", ["h_sym"])
    p.have("e_xb: In b (Singleton x) = (b = x)").by(IN_SINGLETON, "x", "b")
    p.have("h_b_eq_x: b = x").by_eq_mp(p.fact("e_xb"), "h_b_sing")
    p.have("hxb: x = b").by_thm(SYM(p.fact("h_b_eq_x")))

    p.thus("x = a /\\ x = b").by_thm(CONJ(p.fact("hxa"), p.fact("hxb")))


# Lemma:  |- !a b c d. Pair_ord a b = Pair_ord c d ==> (a = c /\ b = d).
#
# Strategy. Pair_ord a b = Pair (Singleton a) (Pair a b), so by IN_PAIR
# the LHS has two members at most: Singleton a and Pair a b. From the
# hypothesis their members coincide with those of Pair_ord c d.
#
# Singleton a is in {Singleton c, Pair c d}, so either Singleton a =
# Singleton c (use SINGLETON_INJ) or Singleton a = Pair c d (use
# SINGLETON_EQ_PAIR -- both c and d collapse to a). Either branch
# yields ``a = c``.
#
# Then Pair a b is in {Singleton c, Pair c d} = {Singleton a, Pair a d}
# (using a = c). Either Pair a b = Singleton a (so by SINGLETON_EQ_PAIR
# applied to its symmetric form: a = b), or Pair a b = Pair a d. In the
# latter case In b (Pair a b) transports to In b (Pair a d), giving
# ``b = a \/ b = d``; in the b = a sub-branch we again collapse via
# SINGLETON_EQ_PAIR. Combined with d's symmetric path, ``b = d`` falls
# out in every branch.
@proof
def PAIR_ORD_INJ(p):
    from fusion import REFL
    from tactics import SYM, CONJ, CONJUNCT1, CONJUNCT2

    p.goal("!a b c d. Pair_ord a b = Pair_ord c d ==> (a = c /\\ b = d)")
    p.fix("a b c d")
    p.assume("h: Pair_ord a b = Pair_ord c d")
    p.have("h_sym: Pair_ord c d = Pair_ord a b").by_thm(SYM(p.fact("h")))

    # ----- Step 1: Singleton a in Pair_ord c d -----
    # In (Singleton a) (Pair_ord a b) holds (left disjunct of IN_PAIR_ORD).
    p.have("hr_sa: Singleton a = Singleton a").by_thm(REFL(p._parse("Singleton a")))
    p.have("hd_sa: Singleton a = Singleton a \\/ Singleton a = Pair a b").by_disj(
        "hr_sa"
    )
    p.have(
        "e_sa: In (Singleton a) (Pair_ord a b) = "
        "(Singleton a = Singleton a \\/ Singleton a = Pair a b)"
    ).by(IN_PAIR_ORD, "a", "b", "Singleton a")
    p.have("h_sa_in_ab: In (Singleton a) (Pair_ord a b)").by_eq_mp(
        SYM(p.fact("e_sa")), "hd_sa"
    )
    # Transport via h.
    p.have("h_sa_in_cd: In (Singleton a) (Pair_ord c d)").by_rewrite_of(
        "h_sa_in_ab", ["h"]
    )
    # IN_PAIR_ORD on Pair_ord c d:  Singleton a = Singleton c \/ Singleton a = Pair c d.
    p.have(
        "e_sa_cd: In (Singleton a) (Pair_ord c d) = "
        "(Singleton a = Singleton c \\/ Singleton a = Pair c d)"
    ).by(IN_PAIR_ORD, "c", "d", "Singleton a")
    p.have("h_sa_disj: Singleton a = Singleton c \\/ Singleton a = Pair c d").by_eq_mp(
        p.fact("e_sa_cd"), "h_sa_in_cd"
    )

    # ----- Step 2: derive a = c -----
    with p.have("h_ac: a = c").proof():
        with p.cases_on("h_sa_disj"):
            with p.case("h1: Singleton a = Singleton c"):
                p.thus("a = c").by(SINGLETON_INJ, "a", "c", "h1")
            with p.case("h2: Singleton a = Pair c d"):
                p.have("h2c: a = c /\\ a = d").by(
                    SINGLETON_EQ_PAIR, "a", "c", "d", "h2"
                )
                p.thus("a = c").by_thm(CONJUNCT1(p.fact("h2c")))

    # ----- Step 3: similarly Pair a b is in Pair_ord c d -----
    p.have("hr_pab: Pair a b = Pair a b").by_thm(REFL(p._parse("Pair a b")))
    p.have("hd_pab: Pair a b = Singleton a \\/ Pair a b = Pair a b").by_disj("hr_pab")
    p.have(
        "e_pab: In (Pair a b) (Pair_ord a b) = "
        "(Pair a b = Singleton a \\/ Pair a b = Pair a b)"
    ).by(IN_PAIR_ORD, "a", "b", "Pair a b")
    p.have("h_pab_in_ab: In (Pair a b) (Pair_ord a b)").by_eq_mp(
        SYM(p.fact("e_pab")), "hd_pab"
    )
    p.have("h_pab_in_cd: In (Pair a b) (Pair_ord c d)").by_rewrite_of(
        "h_pab_in_ab", ["h"]
    )
    p.have(
        "e_pab_cd: In (Pair a b) (Pair_ord c d) = "
        "(Pair a b = Singleton c \\/ Pair a b = Pair c d)"
    ).by(IN_PAIR_ORD, "c", "d", "Pair a b")
    p.have("h_pab_disj: Pair a b = Singleton c \\/ Pair a b = Pair c d").by_eq_mp(
        p.fact("e_pab_cd"), "h_pab_in_cd"
    )

    # ----- Step 4: derive b = d -----
    # We work in the case-on of h_pab_disj. Each branch we resolve via
    # In b (Pair a b) plus IN_PAIR/IN_SINGLETON.
    with p.have("h_bd: b = d").proof():
        # Common: In b (Pair a b) holds (right disjunct of IN_PAIR).
        p.have("hbb: b = b").by_thm(REFL(p._parse("b")))
        p.have("hd_b: b = a \\/ b = b").by_disj("hbb")
        p.have("e_b_in_ab: In b (Pair a b) = (b = a \\/ b = b)").by(
            IN_PAIR, "a", "b", "b"
        )
        p.have("h_b_in_ab: In b (Pair a b)").by_eq_mp(SYM(p.fact("e_b_in_ab")), "hd_b")

        with p.cases_on("h_pab_disj"):
            with p.case("h3: Pair a b = Singleton c"):
                # Singleton c = Pair a b.
                p.have("h3_sym: Singleton c = Pair a b").by_thm(SYM(p.fact("h3")))
                p.have("h3c: c = a /\\ c = b").by(
                    SINGLETON_EQ_PAIR, "c", "a", "b", "h3_sym"
                )
                p.have("h3_cb: c = b").by_thm(CONJUNCT2(p.fact("h3c")))
                p.have("h3_bc: b = c").by_thm(SYM(p.fact("h3_cb")))
                # Now derive d = c (so b = c = d).  Apply Pair_ord_inj
                # idea: also get d via Pair c d in Pair_ord a b.
                # h_sym : Pair_ord c d = Pair_ord a b.
                # In (Pair c d) (Pair_ord c d) holds; transport gives
                # In (Pair c d) (Pair_ord a b).
                p.have("hr_pcd: Pair c d = Pair c d").by_thm(REFL(p._parse("Pair c d")))
                p.have(
                    "hd_pcd: Pair c d = Singleton c \\/ Pair c d = Pair c d"
                ).by_disj("hr_pcd")
                p.have(
                    "e_pcd: In (Pair c d) (Pair_ord c d) = "
                    "(Pair c d = Singleton c \\/ Pair c d = Pair c d)"
                ).by(IN_PAIR_ORD, "c", "d", "Pair c d")
                p.have("h_pcd_in_cd: In (Pair c d) (Pair_ord c d)").by_eq_mp(
                    SYM(p.fact("e_pcd")), "hd_pcd"
                )
                p.have("h_pcd_in_ab: In (Pair c d) (Pair_ord a b)").by_rewrite_of(
                    "h_pcd_in_cd", ["h_sym"]
                )
                p.have(
                    "e_pcd_ab: In (Pair c d) (Pair_ord a b) = "
                    "(Pair c d = Singleton a \\/ Pair c d = Pair a b)"
                ).by(IN_PAIR_ORD, "a", "b", "Pair c d")
                p.have(
                    "h_pcd_disj: Pair c d = Singleton a \\/ Pair c d = Pair a b"
                ).by_eq_mp(p.fact("e_pcd_ab"), "h_pcd_in_ab")
                # In either disjunct Pair c d collapses to Singleton-shape.
                with p.cases_on("h_pcd_disj"):
                    with p.case("h4a: Pair c d = Singleton a"):
                        p.have("h4a_sym: Singleton a = Pair c d").by_thm(
                            SYM(p.fact("h4a"))
                        )
                        p.have("h4a_split: a = c /\\ a = d").by(
                            SINGLETON_EQ_PAIR, "a", "c", "d", "h4a_sym"
                        )
                        p.have("h4a_d: a = d").by_thm(CONJUNCT2(p.fact("h4a_split")))
                        # b = c = a (from h3_bc and h_ac).
                        p.have("h_ba: b = a").by_rewrite_of(
                            "h3_bc", [SYM(p.fact("h_ac"))]
                        )
                        # b = a = d.
                        p.thus("b = d").by_rewrite_of("h_ba", ["h4a_d"])
                    with p.case("h4b: Pair c d = Pair a b"):
                        # Pair c d = Pair a b. We have b = c (h3_bc).
                        # In d (Pair c d) holds.
                        p.have("hdd: d = d").by_thm(REFL(p._parse("d")))
                        p.have("hd_d: d = c \\/ d = d").by_disj("hdd")
                        p.have("e_d_cd: In d (Pair c d) = (d = c \\/ d = d)").by(
                            IN_PAIR, "c", "d", "d"
                        )
                        p.have("h_d_cd: In d (Pair c d)").by_eq_mp(
                            SYM(p.fact("e_d_cd")), "hd_d"
                        )
                        p.have("h_d_ab: In d (Pair a b)").by_rewrite_of(
                            "h_d_cd", ["h4b"]
                        )
                        p.have("e_d_ab: In d (Pair a b) = (d = a \\/ d = b)").by(
                            IN_PAIR, "a", "b", "d"
                        )
                        p.have("h_d_disj: d = a \\/ d = b").by_eq_mp(
                            p.fact("e_d_ab"), "h_d_ab"
                        )
                        with p.cases_on("h_d_disj"):
                            with p.case("h5a: d = a"):
                                # a = b (because Pair a b = Singleton c
                                # forces b = c = a; via h3_bc + h_ac).
                                p.have("h_ba: b = a").by_rewrite_of(
                                    "h3_bc", [SYM(p.fact("h_ac"))]
                                )
                                p.have("h5a_sym: a = d").by_thm(SYM(p.fact("h5a")))
                                p.thus("b = d").by_rewrite_of("h_ba", ["h5a_sym"])
                            with p.case("h5b: d = b"):
                                p.thus("b = d").by_thm(SYM(p.fact("h5b")))
            with p.case("h6: Pair a b = Pair c d"):
                # h_ac : a = c.  So Pair a b = Pair a d.
                # In b (Pair a b) holds; transport gives In b (Pair a d).
                p.have("h6c: Pair a b = Pair a d").by_rewrite_of(
                    "h6", [SYM(p.fact("h_ac"))]
                )
                p.have("h_b_in_ad: In b (Pair a d)").by_rewrite_of("h_b_in_ab", ["h6c"])
                p.have("e_b_ad: In b (Pair a d) = (b = a \\/ b = d)").by(
                    IN_PAIR, "a", "d", "b"
                )
                p.have("h_b_disj: b = a \\/ b = d").by_eq_mp(
                    p.fact("e_b_ad"), "h_b_in_ad"
                )
                with p.cases_on("h_b_disj"):
                    with p.case("h7a: b = a"):
                        # Pair a b = Pair a a = Singleton a (using
                        # SINGLETON_EQ_PAIR's symmetric form).  We must
                        # show b = d.  Pair a b = Pair a d under b = a:
                        # In d (Pair a d) holds; transport via SYM gives
                        # In d (Pair a b) = In d (Pair a a). Apply
                        # IN_PAIR: d = a \/ d = a, so d = a. And b = a.
                        p.have("hdd: d = d").by_thm(REFL(p._parse("d")))
                        p.have("hd_d: d = a \\/ d = d").by_disj("hdd")
                        p.have("e_d_ad: In d (Pair a d) = (d = a \\/ d = d)").by(
                            IN_PAIR, "a", "d", "d"
                        )
                        p.have("h_d_ad: In d (Pair a d)").by_eq_mp(
                            SYM(p.fact("e_d_ad")), "hd_d"
                        )
                        p.have("h6c_sym: Pair a d = Pair a b").by_thm(
                            SYM(p.fact("h6c"))
                        )
                        p.have("h_d_ab: In d (Pair a b)").by_rewrite_of(
                            "h_d_ad", ["h6c_sym"]
                        )
                        # Pair a b = Pair a a (under b = a).
                        p.have("h7a_sym: a = b").by_thm(SYM(p.fact("h7a")))
                        p.have("h_d_aa: In d (Pair a a)").by_rewrite_of(
                            "h_d_ab", ["h7a_sym"]
                        )
                        p.have("e_d_aa: In d (Pair a a) = (d = a \\/ d = a)").by(
                            IN_PAIR, "a", "a", "d"
                        )
                        p.have("h_d_disj_aa: d = a \\/ d = a").by_eq_mp(
                            p.fact("e_d_aa"), "h_d_aa"
                        )
                        with p.cases_on("h_d_disj_aa"):
                            with p.case("h8a: d = a"):
                                # b = a, d = a -> b = d.
                                p.have("h_da: a = d").by_thm(SYM(p.fact("h8a")))
                                p.thus("b = d").by_rewrite_of("h7a", ["h_da"])
                            with p.case("h8b: d = a"):
                                p.have("h_da: a = d").by_thm(SYM(p.fact("h8b")))
                                p.thus("b = d").by_rewrite_of("h7a", ["h_da"])
                    with p.case("h7b: b = d"):
                        p.thus("b = d").by_thm(p.fact("h7b"))

    p.thus("a = c /\\ b = d").by_thm(CONJ(p.fact("h_ac"), p.fact("h_bd")))


# Lemma:  |- !a b. nat0_lt a (Pair_ord a b).
#
# Chain a in Pair a b (left disjunct of IN_PAIR), Pair a b in Pair_ord
# a b (right disjunct of IN_PAIR_ORD), and lift each to nat0_lt via
# IN_LT, with a single NAT0_LT_TRANS.
@proof
def NAT0_LT_PAIR_ORD_L(p):
    from fusion import REFL
    from tactics import SYM
    from nat0_order import NAT0_LT_TRANS

    p.goal("!a b. nat0_lt a (Pair_ord a b)")
    p.fix("a b")
    # In a (Pair a b) via left disjunct.
    p.have("haa: a = a").by_thm(REFL(p._parse("a")))
    p.have("hd_a: a = a \\/ a = b").by_disj("haa")
    p.have("e_a: In a (Pair a b) = (a = a \\/ a = b)").by(IN_PAIR, "a", "b", "a")
    p.have("h_a_in_pair: In a (Pair a b)").by_eq_mp(SYM(p.fact("e_a")), "hd_a")
    p.have("h_a_lt_pair: nat0_lt a (Pair a b)").by(
        IN_LT, "Pair a b", "a", "h_a_in_pair"
    )
    # In (Pair a b) (Pair_ord a b) via right disjunct of IN_PAIR_ORD.
    p.have("hr_p: Pair a b = Pair a b").by_thm(REFL(p._parse("Pair a b")))
    p.have("hd_p: Pair a b = Singleton a \\/ Pair a b = Pair a b").by_disj("hr_p")
    p.have(
        "e_p: In (Pair a b) (Pair_ord a b) = "
        "(Pair a b = Singleton a \\/ Pair a b = Pair a b)"
    ).by(IN_PAIR_ORD, "a", "b", "Pair a b")
    p.have("h_p_in_po: In (Pair a b) (Pair_ord a b)").by_eq_mp(
        SYM(p.fact("e_p")), "hd_p"
    )
    p.have("h_p_lt_po: nat0_lt (Pair a b) (Pair_ord a b)").by(
        IN_LT, "Pair_ord a b", "Pair a b", "h_p_in_po"
    )
    p.thus("nat0_lt a (Pair_ord a b)").by(
        NAT0_LT_TRANS,
        "a",
        "Pair a b",
        "Pair_ord a b",
        "h_a_lt_pair",
        "h_p_lt_po",
    )


# Lemma:  |- !a b. nat0_lt b (Pair_ord a b).  (Symmetric to L; right disjunct.)
@proof
def NAT0_LT_PAIR_ORD_R(p):
    from fusion import REFL
    from tactics import SYM
    from nat0_order import NAT0_LT_TRANS

    p.goal("!a b. nat0_lt b (Pair_ord a b)")
    p.fix("a b")
    p.have("hbb: b = b").by_thm(REFL(p._parse("b")))
    p.have("hd_b: b = a \\/ b = b").by_disj("hbb")
    p.have("e_b: In b (Pair a b) = (b = a \\/ b = b)").by(IN_PAIR, "a", "b", "b")
    p.have("h_b_in_pair: In b (Pair a b)").by_eq_mp(SYM(p.fact("e_b")), "hd_b")
    p.have("h_b_lt_pair: nat0_lt b (Pair a b)").by(
        IN_LT, "Pair a b", "b", "h_b_in_pair"
    )
    p.have("hr_p: Pair a b = Pair a b").by_thm(REFL(p._parse("Pair a b")))
    p.have("hd_p: Pair a b = Singleton a \\/ Pair a b = Pair a b").by_disj("hr_p")
    p.have(
        "e_p: In (Pair a b) (Pair_ord a b) = "
        "(Pair a b = Singleton a \\/ Pair a b = Pair a b)"
    ).by(IN_PAIR_ORD, "a", "b", "Pair a b")
    p.have("h_p_in_po: In (Pair a b) (Pair_ord a b)").by_eq_mp(
        SYM(p.fact("e_p")), "hd_p"
    )
    p.have("h_p_lt_po: nat0_lt (Pair a b) (Pair_ord a b)").by(
        IN_LT, "Pair_ord a b", "Pair a b", "h_p_in_po"
    )
    p.thus("nat0_lt b (Pair_ord a b)").by(
        NAT0_LT_TRANS,
        "b",
        "Pair a b",
        "Pair_ord a b",
        "h_b_lt_pair",
        "h_p_lt_po",
    )


# ---------------------------------------------------------------------------
# Stage 3 (cont.) -- Union a b   ( bit-OR on two HF sets ).
#
# Definition (well-founded recursion on the first arg via HALF):
#   Union n m = m                                      when n = 0
#             = COND (ODD n \/ ODD m)
#                    (SUC0 (double (Union (HALF n) (HALF m))))
#                    (double (Union (HALF n) (HALF m)))   when ~(n = 0)
#
# Justification: HALF n < n for n != 0 (HALF_LT_NZ), so the recursion is
# well-founded under nat0_lt; the body packs the OR of low bits onto the
# doubled recursive result, recovering the bit-or value.
#
# Characterisation: |- !x a b. In x (Union a b) = In x a \/ In x b
# (IN_UNION). This is the only consumer-facing fact -- everything else
# (the recursion equations, the helper _union_F constant) is internal
# scaffolding.
# ---------------------------------------------------------------------------

from nat0_order import define_wf_lt as _define_wf_lt  # noqa: E402

from bits import (  # noqa: E402
    ODD,  # noqa: F401  -- parser alias
    HALF,  # noqa: F401  -- parser alias
    double,  # noqa: F401  -- parser alias
    HALF_LT_NZ,
    HALF_BASE,
    BIT_BASE,
    BIT_STEP_AT,
    HALF_DOUBLE,
    HALF_SUC0_DOUBLE,
    ODD_DOUBLE,
    ODD_SUC0_DOUBLE,
    COND_T_NAT0,
    COND_F_NAT0,
)
from classical import EXCLUDED_MIDDLE  # noqa: E402


_F_union_ty = parse_type("(nat0 -> nat0 -> nat0) -> nat0 -> nat0 -> nat0")
_union_fn_ty = parse_type("nat0 -> nat0 -> nat0")


_UNION_F_DEF = define(
    "_union_F",
    _F_union_ty,
    "\\f:nat0->nat0->nat0. \\n:nat0. \\m:nat0. "
    "COND_nat0 (n = 0) m "
    "(COND_nat0 (ODD n \\/ ODD m) "
    "  (SUC0 (double (f (HALF n) (HALF m)))) "
    "  (double (f (HALF n) (HALF m))))",
)
_union_F = mk_const("_union_F", [])


# Pointwise / beta-normalised form:
#   |- !f n m. _union_F f n m =
#                COND_nat0 (n = 0) m
#                  (COND_nat0 (ODD n \/ ODD m)
#                             (SUC0 (double (f (HALF n) (HALF m))))
#                             (double (f (HALF n) (HALF m)))).
# REWRITE_CONV doesn't beta-reduce (\f n m. body) f n m by itself, so we
# do the three AP_THM/BETA_CONV peels here once and use this fully-applied
# form as the unfolder downstream.
def _prove_union_F_at():
    from tactics import AP_THM, BETA_CONV, TRANS, GENL

    _f_var = Var("f", _union_fn_ty)
    _n_var = Var("n", nat0_ty)
    _m_var = Var("m", nat0_ty)
    th_f = AP_THM(_UNION_F_DEF, _f_var)
    th_f_eq = TRANS(th_f, BETA_CONV(rand(th_f._concl)))
    th_fn = AP_THM(th_f_eq, _n_var)
    th_fn_eq = TRANS(th_fn, BETA_CONV(rand(th_fn._concl)))
    th_fnm = AP_THM(th_fn_eq, _m_var)
    th_fnm_eq = TRANS(th_fnm, BETA_CONV(rand(th_fnm._concl)))
    return GENL([_f_var, _n_var, _m_var], th_fnm_eq)


_UNION_F_AT = _prove_union_F_at()


@proof
def UNION_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                 ==> _union_F f n = _union_F g n."""
    from tactics import AP_THM, EQF_INTRO, EQT_INTRO

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> _union_F f n = _union_F g n",
        types={
            "f": _union_fn_ty,
            "g": _union_fn_ty,
            "n": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    # Prove the pointwise equality at every m, then by_ext to get the
    # function equality _union_F f n = _union_F g n.
    with p.have("ext: !m. _union_F f n m = _union_F g n m").proof():
        p.fix("m")
        with p.cases_on(EXCLUDED_MIDDLE, "n = 0"):
            with p.case("hz: n = 0"):
                # Both sides of the body collapse to the outer THEN-branch (m).
                p.have("hz_eq: (n = 0) = T").by_thm(EQT_INTRO(p.fact("hz")))
                p.thus("_union_F f n m = _union_F g n m").by_rewrite(
                    [_UNION_F_AT, "hz_eq", COND_T_NAT0]
                )
            with p.case("hnz: ~(n = 0)"):
                # HALF n < n -> the IH at HALF n gives f (HALF n) = g (HALF n).
                p.have("hlt: nat0_lt (HALF n) n").by(HALF_LT_NZ, "n", "hnz")
                p.have("hfg: f (HALF n) = g (HALF n)").by("h", "HALF n", "hlt")
                p.have(
                    "hfg_m: f (HALF n) (HALF m) = g (HALF n) (HALF m)"
                ).by_thm(AP_THM(p.fact("hfg"), p._parse("HALF m")))
                p.have("hnz_eq: (n = 0) = F").by_thm(EQF_INTRO(p.fact("hnz")))
                p.thus("_union_F f n m = _union_F g n m").by_rewrite(
                    [_UNION_F_AT, "hnz_eq", COND_F_NAT0, "hfg_m"]
                )
    p.thus("_union_F f n = _union_F g n").by_ext("ext")


# Well-founded recursive definition.
#   UNION_DEF : |- Union = (@h. !n. h n = _union_F h n)
#   UNION_REC : |- !n. Union n = _union_F Union n
UNION_DEF, UNION_REC = _define_wf_lt(
    "Union",
    parse_type("nat0 -> nat0 -> nat0"),
    _union_F,
    UNION_MONO,
)
Union = mk_const("Union", [])


# Unfolding equations.
#   UNION_AT  : |- !n m. Union n m = body[Union, n, m]   (raw recursion)
#   UNION_AT_ZERO : |- !m. Union 0 m = m
#   UNION_AT_NZ   : |- !n m. ~(n = 0) ==>
#                       Union n m =
#                         COND_nat0 (ODD n \/ ODD m)
#                           (SUC0 (double (Union (HALF n) (HALF m))))
#                           (double (Union (HALF n) (HALF m)))
#
# Cannot use UNION_REC as a generic ``by_rewrite`` rule because its RHS
# (``_union_F Union n``) keeps producing fresh ``Union`` applications under
# ``_UNION_F_AT`` -- the rewriter never reaches a fixpoint. Instead, SPEC
# UNION_REC once at the target ``n``, AP_THM through ``m``, then chain
# through ``_UNION_F_AT`` and the relevant COND collapse.


def _prove_union_at():
    """|- !n m. Union n m = body[Union, n, m]."""
    from tactics import SPEC, SPECL, AP_THM, TRANS, GENL

    n_v = Var("n", nat0_ty)
    m_v = Var("m", nat0_ty)
    union_n = SPEC(n_v, UNION_REC)
    union_n_m = AP_THM(union_n, m_v)
    F_at_n_m = SPECL([Union, n_v, m_v], _UNION_F_AT)
    return GENL([n_v, m_v], TRANS(union_n_m, F_at_n_m))


UNION_AT = _prove_union_at()


def _prove_union_at_zero():
    """|- !m. Union 0 m = m."""
    from tactics import SPECL, REWRITE_RULE, EQT_INTRO, GEN
    from fusion import REFL

    m_v = Var("m", nat0_ty)
    base = SPECL([ZERO, m_v], UNION_AT)
    # base : |- Union 0 m = COND_nat0 (0 = 0) m (...).
    simp = REWRITE_RULE([EQT_INTRO(REFL(ZERO)), COND_T_NAT0], base)
    # simp : |- Union 0 m = m.
    return GEN(m_v, simp)


UNION_AT_ZERO = _prove_union_at_zero()


@proof
def UNION_AT_NZ(p):
    from tactics import EQF_INTRO, SPECL

    p.goal(
        "!n m. ~(n = 0) ==> Union n m = "
        "COND_nat0 (ODD n \\/ ODD m) "
        "  (SUC0 (double (Union (HALF n) (HALF m)))) "
        "  (double (Union (HALF n) (HALF m)))"
    )
    p.fix("n m")
    p.assume("hnz: ~(n = 0)")
    p.have("base: Union n m = "
           "COND_nat0 (n = 0) m "
           "(COND_nat0 (ODD n \\/ ODD m) "
           "  (SUC0 (double (Union (HALF n) (HALF m)))) "
           "  (double (Union (HALF n) (HALF m))))").by(UNION_AT, "n", "m")
    p.have("hnz_eq: (n = 0) = F").by_thm(EQF_INTRO(p.fact("hnz")))
    p.thus(
        "Union n m = "
        "COND_nat0 (ODD n \\/ ODD m) "
        "  (SUC0 (double (Union (HALF n) (HALF m)))) "
        "  (double (Union (HALF n) (HALF m)))"
    ).by_rewrite_of("base", ["hnz_eq", COND_F_NAT0])


# Bit/bit-position structure of Union: HALF and ODD distribute through it.
#   UNION_HALF : |- !a b. HALF (Union a b) = Union (HALF a) (HALF b)
#   UNION_ODD  : |- !a b. ODD  (Union a b) = (ODD a \/ ODD b)
# Both proved by case-split on a = 0 (use UNION_AT_ZERO) versus
# ~(a = 0) (UNION_AT_NZ + sub-case-split on the OR-of-low-bits guard
# selecting which arm of the inner COND was taken).


@proof
def UNION_HALF(p):
    from tactics import EQT_INTRO, EQF_INTRO

    p.goal("!a b. HALF (Union a b) = Union (HALF a) (HALF b)")
    p.fix("a b")
    with p.cases_on(EXCLUDED_MIDDLE, "a = 0"):
        with p.case("hz: a = 0"):
            p.thus("HALF (Union a b) = Union (HALF a) (HALF b)").by_rewrite(
                [UNION_AT_ZERO, "hz", HALF_BASE]
            )
        with p.case("hnz: ~(a = 0)"):
            p.have(
                "hu: Union a b = "
                "COND_nat0 (ODD a \\/ ODD b) "
                "  (SUC0 (double (Union (HALF a) (HALF b)))) "
                "  (double (Union (HALF a) (HALF b)))"
            ).by(UNION_AT_NZ, "a", "b", "hnz")
            with p.cases_on(EXCLUDED_MIDDLE, "ODD a \\/ ODD b"):
                with p.case("hOd: ODD a \\/ ODD b"):
                    p.have("hOd_eq: (ODD a \\/ ODD b) = T").by_thm(
                        EQT_INTRO(p.fact("hOd"))
                    )
                    p.have(
                        "hu_T: Union a b = SUC0 (double (Union (HALF a) (HALF b)))"
                    ).by_rewrite_of("hu", ["hOd_eq", COND_T_NAT0])
                    p.thus(
                        "HALF (Union a b) = Union (HALF a) (HALF b)"
                    ).by_rewrite(["hu_T", HALF_SUC0_DOUBLE])
                with p.case("hnOd: ~(ODD a \\/ ODD b)"):
                    p.have("hnOd_eq: (ODD a \\/ ODD b) = F").by_thm(
                        EQF_INTRO(p.fact("hnOd"))
                    )
                    p.have(
                        "hu_F: Union a b = double (Union (HALF a) (HALF b))"
                    ).by_rewrite_of("hu", ["hnOd_eq", COND_F_NAT0])
                    p.thus(
                        "HALF (Union a b) = Union (HALF a) (HALF b)"
                    ).by_rewrite(["hu_F", HALF_DOUBLE])


@proof
def UNION_ODD(p):
    from tactics import EQT_INTRO, EQF_INTRO, OR_F_LEFT
    from bits import ODD_BASE

    p.goal("!a b. ODD (Union a b) = (ODD a \\/ ODD b)")
    p.fix("a b")
    with p.cases_on(EXCLUDED_MIDDLE, "a = 0"):
        with p.case("hz: a = 0"):
            # ODD (Union 0 b) = ODD b; RHS: ODD 0 \/ ODD b = F \/ ODD b = ODD b.
            p.thus("ODD (Union a b) = (ODD a \\/ ODD b)").by_rewrite(
                [UNION_AT_ZERO, "hz", ODD_BASE, OR_F_LEFT]
            )
        with p.case("hnz: ~(a = 0)"):
            p.have(
                "hu: Union a b = "
                "COND_nat0 (ODD a \\/ ODD b) "
                "  (SUC0 (double (Union (HALF a) (HALF b)))) "
                "  (double (Union (HALF a) (HALF b)))"
            ).by(UNION_AT_NZ, "a", "b", "hnz")
            with p.cases_on(EXCLUDED_MIDDLE, "ODD a \\/ ODD b"):
                with p.case("hOd: ODD a \\/ ODD b"):
                    p.have("hOd_eq: (ODD a \\/ ODD b) = T").by_thm(
                        EQT_INTRO(p.fact("hOd"))
                    )
                    p.have(
                        "hu_T: Union a b = SUC0 (double (Union (HALF a) (HALF b)))"
                    ).by_rewrite_of("hu", ["hOd_eq", COND_T_NAT0])
                    # ODD (SUC0 (double Z)) = T; RHS = T.
                    p.thus("ODD (Union a b) = (ODD a \\/ ODD b)").by_rewrite(
                        ["hu_T", ODD_SUC0_DOUBLE, "hOd_eq"]
                    )
                with p.case("hnOd: ~(ODD a \\/ ODD b)"):
                    p.have("hnOd_eq: (ODD a \\/ ODD b) = F").by_thm(
                        EQF_INTRO(p.fact("hnOd"))
                    )
                    p.have(
                        "hu_F: Union a b = double (Union (HALF a) (HALF b))"
                    ).by_rewrite_of("hu", ["hnOd_eq", COND_F_NAT0])
                    # ODD (double Z) = F; RHS = F.
                    p.thus("ODD (Union a b) = (ODD a \\/ ODD b)").by_rewrite(
                        ["hu_F", ODD_DOUBLE, "hnOd_eq"]
                    )


# Helper: |- !x y. In (SUC0 x) y = In x (HALF y).
# Mirror of BIT_STEP_AT under IN_AT, kept in In-form so it composes with
# In-shaped IHs without flipping back through bit/In conversions.
@proof
def IN_SUCC_AT(p):
    p.goal("!x y. In (SUC0 x) y = In x (HALF y)")
    p.fix("x y")
    p.thus("In (SUC0 x) y = In x (HALF y)").by_rewrite([IN_AT, BIT_STEP_AT])


# Membership characterisation:
#   IN_UNION : |- !x a b. In x (Union a b) = (In x a \/ In x b).
# Peano induction on x; UNION_ODD discharges the bit-0 case and
# UNION_HALF + the IH (re-instantiated at HALF a, HALF b) discharges
# the bit-(SUC0 x) case.


@proof
def IN_UNION(p):
    p.goal("!x a b. In x (Union a b) = (In x a \\/ In x b)")
    with p.induction("x"):
        with p.base():
            p.fix("a b")
            # In 0 y = bit 0 y = ODD y; combine with UNION_ODD.
            p.thus("In 0 (Union a b) = (In 0 a \\/ In 0 b)").by_rewrite(
                [IN_AT, BIT_BASE, UNION_ODD]
            )
        with p.step("IH"):
            p.fix("a b")
            # In (SUC0 x) y = In x (HALF y) (IN_SUCC_AT);
            # HALF (Union a b) = Union (HALF a) (HALF b) (UNION_HALF);
            # IH at HALF a, HALF b lifts the inner Union to a disjunction.
            p.have(
                "hIH: In x (Union (HALF a) (HALF b)) "
                "= (In x (HALF a) \\/ In x (HALF b))"
            ).by("IH", "HALF a", "HALF b")
            p.thus(
                "In (SUC0 x) (Union a b) = (In (SUC0 x) a \\/ In (SUC0 x) b)"
            ).by_rewrite([IN_SUCC_AT, UNION_HALF, "hIH"])


# ---------------------------------------------------------------------------
# Stage 4 -- canonical vN embedding + Peano facts on nat0.
# ---------------------------------------------------------------------------
#
# Two pieces:
#
#   (a) The canonical von Neumann embedding vN : nat0 -> hf, with
#       its successor and the injectivity / nonzeroness lemmas. This
#       is the "right" embedding of N into HF and is independently
#       useful for syntax-encoding work (every numeral has a canonical
#       HF representation).
#
#   (b) Peano-arithmetic facts on nat0. ``SUC0`` / ``n0plus`` /
#       ``n0times`` satisfy the seven Peano equations (PEANO_1..PEANO_7
#       below). Originally these mirrored Robinson's Q1-Q7 as the
#       HF-model interpretation; after the switch to pure HF as the
#       object theory the equations stand on their own.
#
# ---------- (a) The canonical vN embedding ----------
#
#   vN 0       := Empty                                          ( = 0 )
#   vN (S n)   := vN_succ (vN n)
#                where vN_succ x := Union (Pair x (Singleton x))
#                                = Insert x x
#                                  -- equivalent in HF; the latter is
#                                  -- one bit-flip and avoids the
#                                  -- ordered-pair detour. Both forms
#                                  -- agree because Singleton x = {x}
#                                  -- and Union {x, {x}} = x ∪ {x}.
#
# Lemmas (all proved below):
#
#   VN_SUCC_NEQ_ZERO  :  |- !x. ~(vN_succ x = Empty)
#     Universal over hf, not just over the vN image. ``vN_succ x =
#     Insert x x`` has bit x set (IN_INSERT_SAME) whereas Empty has
#     none (NOT_IN_EMPTY); congruence on the assumed equation
#     contradicts NOT_IN_EMPTY.    ~8 lines.
#
#   VN_SUCC_INJ        :  |- !m n. vN_succ m = vN_succ n ==> m = n
#     Proof: case-split on m = n. In the negative branch,
#     BIT_AT_SET_BIT_SAME at i = m gives ``bit m (set_bit m m) = T``;
#     BIT_AT_SET_BIT_DIFF at j = m, i = n collapses
#     ``bit m (set_bit n n)`` to ``bit m n``; bit-equality from the
#     hypothesis then forces ``bit m n = T``, whence BIT_LT gives
#     nat0_lt m n. Symmetric argument gives nat0_lt n m, contradicting
#     NAT0_LT_ASYM (lifted from num via _SATZ_9_EXCL_13).    ~35 lines.
#
#   VN_INJ             :  |- !m n. vN m = vN n ==> m = n
#     Doubly-nested nat0 induction: the off-diagonal cases collapse
#     to ``vN_succ y = Empty`` and apply VN_SUCC_NEQ_ZERO; the diagonal
#     step peels successors via VN_SUCC_INJ + outer IH.    ~25 lines.
#
#   VN_PRED            :  |- !n. ~(vN n = Empty) ==> ?y. vN n = vN_succ y
#     Image-restricted predecessor. The universal-over-hf form
#     ``!x. ~(x = Empty) ==> ?y. x = vN_succ y`` is *not* provable:
#     vN_succ is not surjective on hf (e.g. {1} = 2 has no vN-
#     predecessor since vN_succ y = set_bit y y ≠ 2 for every y).
#     One-step nat0 induction.    ~10 lines.
#
# ---------- (b) Peano arithmetic on nat0 ----------
#
#   defn:  n0plus  : nat0 -> nat0 -> nat0   (Peano + on nat0)
#          n0times : nat0 -> nat0 -> nat0   (Peano * on nat0)
#     defined via define_recursive_0 by recursion on the second arg.
#
#   thm:   PEANO_1 :  |- !n.   ~(SUC0 n = Empty)
#          PEANO_2 :  |- !m n. SUC0 m = SUC0 n ==> m = n
#          PEANO_3 :  |- !x.   ~(x = Empty) ==> ?y. x = SUC0 y
#          PEANO_4 :  |- !x.   n0plus x Empty = x
#          PEANO_5 :  |- !x y. n0plus x (SUC0 y) = SUC0 (n0plus x y)
#          PEANO_6 :  |- !x.   n0times x Empty = Empty
#          PEANO_7 :  |- !x y. n0times x (SUC0 y) = n0plus (n0times x y) x
#
#     PEANO_1 reduces to AXIOM_3_0 modulo EMPTY_DEF; PEANO_2 is
#     AXIOM_4_0 verbatim; PEANO_3 is one nat0 induction; PEANO_4..7
#     are the BASE/STEP theorems returned by define_recursive_0
#     modulo EMPTY_DEF. ~50 lines total for the seven lemmas plus the
#     two recursive definitions.
#
# The vN/vN_succ block above is consumed by godel_first.py Stage 1 for
# syntax encoding: each numeral that appears inside an HF-formula gets
# a definite HF code via vN.

VN_SUCC_DEF = define(
    "vN_succ",
    parse_type("nat0 -> nat0"),
    "\\x:nat0. Insert x x",
)
vN_succ = mk_const("vN_succ", [])


# Pointwise: |- !x. vN_succ x = Insert x x.
def _prove_vn_succ_at():
    from tactics import AP_THM, BETA_CONV, TRANS, GEN

    th_x = AP_THM(VN_SUCC_DEF, _x_n0)
    return GEN(_x_n0, TRANS(th_x, BETA_CONV(rand(th_x._concl))))


VN_SUCC_AT = _prove_vn_succ_at()


# ---------------------------------------------------------------------------
# Lemma:  |- !x. ~(vN_succ x = Empty).
# Bit ``x`` is set in ``vN_succ x = Insert x x = set_bit x x`` (by
# BIT_AT_SET_BIT_SAME, equivalently IN_INSERT_SAME) but is unset in
# Empty = 0 (BIT_AT_ZERO / NOT_IN_EMPTY). Substituting ``Empty`` for
# ``vN_succ x`` along the assumed equation contradicts NOT_IN_EMPTY.
# ---------------------------------------------------------------------------


@proof
def VN_SUCC_NEQ_ZERO(p):
    from tactics import EQT_ELIM

    p.goal("!x. ~(vN_succ x = Empty)")
    p.fix("x")
    with p.suppose("h: vN_succ x = Empty"):
        p.have("hT: In x (vN_succ x) = T").by_rewrite([VN_SUCC_AT, IN_INSERT_SAME])
        p.have("hET: In x Empty = T").by_rewrite_of("hT", ["h"])
        p.have("hP: In x Empty").by_thm(EQT_ELIM(p.fact("hET")))
        p.have("hN: ~In x Empty").by(NOT_IN_EMPTY, "x")
        p.absurd().by_conj("hN", "hP")


# ---------------------------------------------------------------------------
# vN -- the von Neumann embedding nat0 -> hf.
#   vN 0       = Empty
#   vN (SUC0 n) = vN_succ (vN n)
# ---------------------------------------------------------------------------

_n_n0 = Var("n", nat0_ty)
_a_hf = Var("a", nat0_ty)

_h_vn = mk_abs(_n_n0, mk_abs(_a_hf, mk_app(vN_succ, _a_hf)))
VN_BASE, VN_STEP = define_unary_0(
    "vN",
    parse_type("nat0 -> nat0"),
    Empty,
    _h_vn,
    result_ty=nat0_ty,
)
vN = mk_const("vN", [])


# ---------------------------------------------------------------------------
# Lemma:  |- !m n. vN_succ m = vN_succ n ==> m = n.
#
# vN_succ x = set_bit x x. Suppose vN_succ m = vN_succ n. Case-split
# on m = n; in the negative branch, instantiate bit-extensionality at
# i = m and i = n.
#
#   bit m (set_bit m m) = T            (BIT_AT_SET_BIT_SAME)
#   bit m (set_bit n n) = bit m n      (BIT_AT_SET_BIT_DIFF, ~(n = m))
# whence bit m n, then nat0_lt m n by BIT_LT. By symmetry, nat0_lt n m,
# contradicting NAT0_LT_ASYM.
# ---------------------------------------------------------------------------


@proof
def VN_SUCC_INJ(p):
    from classical import EXCLUDED_MIDDLE
    from tactics import EQT_ELIM, SYM

    p.goal("!m n. vN_succ m = vN_succ n ==> m = n")
    p.fix("m n")
    p.assume("h: vN_succ m = vN_succ n")
    with p.cases_on(EXCLUDED_MIDDLE, "m = n"):
        with p.case("hmn: m = n"):
            p.thus("m = n").by_thm(p.fact("hmn"))
        with p.case("hnmn: ~(m = n)"):
            with p.have("h_nm: ~(n = m)").proof():
                with p.suppose("hnm: n = m"):
                    p.have("hmn2: m = n").by_thm(SYM(p.fact("hnm")))
                    p.absurd().by_conj("hnmn", "hmn2")
            # Express vN_succ as set_bit.
            p.have("h_set: set_bit m m = set_bit n n").by_rewrite_of(
                "h", [VN_SUCC_AT, INSERT_AT]
            )
            # Direction 1: bit m (set_bit m m) = T, transport via h_set,
            # then BIT_AT_SET_BIT_DIFF gives bit m n = T.
            p.have("h_bm: bit m (set_bit m m) = T").by(BIT_AT_SET_BIT_SAME, "m", "m")
            p.have("h_bm_n: bit m (set_bit n n) = T").by_rewrite_of("h_bm", ["h_set"])
            p.have("h_diff_n: bit m (set_bit n n) = bit m n").by(
                BIT_AT_SET_BIT_DIFF, "n", "m", "n", "h_nm"
            )
            p.have("h_bit_mn: bit m n = T").by_rewrite_of("h_bm_n", ["h_diff_n"])
            p.have("h_bmn_pos: bit m n").by_thm(EQT_ELIM(p.fact("h_bit_mn")))
            p.have("h_lt_mn: nat0_lt m n").by(BIT_LT, "n", "m", "h_bmn_pos")
            # Direction 2 (symmetric).
            p.have("h_bn: bit n (set_bit n n) = T").by(BIT_AT_SET_BIT_SAME, "n", "n")
            p.have("h_set_sym: set_bit n n = set_bit m m").by_thm(SYM(p.fact("h_set")))
            p.have("h_bn_m: bit n (set_bit m m) = T").by_rewrite_of(
                "h_bn", ["h_set_sym"]
            )
            p.have("h_diff_m: bit n (set_bit m m) = bit n m").by(
                BIT_AT_SET_BIT_DIFF, "m", "n", "m", "hnmn"
            )
            p.have("h_bit_nm: bit n m = T").by_rewrite_of("h_bn_m", ["h_diff_m"])
            p.have("h_bnm_pos: bit n m").by_thm(EQT_ELIM(p.fact("h_bit_nm")))
            p.have("h_lt_nm: nat0_lt n m").by(BIT_LT, "m", "n", "h_bnm_pos")
            # Asymmetry contradiction.
            p.have("h_nasym: ~(nat0_lt n m)").by(NAT0_LT_ASYM, "m", "n", "h_lt_mn")
            p.absurd().by_conj("h_nasym", "h_lt_nm")


# ---------------------------------------------------------------------------
# Lemma:  |- !m n. vN m = vN n ==> m = n.
#
# Doubly-nested induction. The off-diagonal cases reduce to
# ``vN_succ x = Empty`` and apply VN_SUCC_NEQ_ZERO; the diagonal step
# uses VN_SUCC_INJ to peel the successors and the outer IH to finish.
# ---------------------------------------------------------------------------


@proof
def VN_INJ(p):
    from fusion import REFL
    from tactics import SYM

    SUC0_c = mk_const("SUC0", [])

    p.goal("!m n. vN m = vN n ==> m = n")
    with p.induction("m"):
        with p.base():
            # Goal: !n. vN 0 = vN n ==> 0 = n.
            with p.induction("n"):
                with p.base():
                    p.assume("h: vN 0 = vN 0")
                    p.thus("0 = 0").by_thm(REFL(ZERO))
                with p.step("IH_n_unused"):
                    p.assume("h: vN 0 = vN (SUC0 n)")
                    p.have("h_eq: Empty = vN_succ (vN n)").by_rewrite_of(
                        "h", [VN_BASE, VN_STEP]
                    )
                    p.have("h_sym: vN_succ (vN n) = Empty").by_thm(SYM(p.fact("h_eq")))
                    p.have("h_neq: ~(vN_succ (vN n) = Empty)").by(
                        VN_SUCC_NEQ_ZERO, "vN n"
                    )
                    p.absurd().by_conj("h_neq", "h_sym")
        with p.step("IH"):
            # IH: !n. vN m = vN n ==> m = n.
            # Goal: !n. vN (SUC0 m) = vN n ==> SUC0 m = n.
            with p.induction("n"):
                with p.base():
                    p.assume("h: vN (SUC0 m) = vN 0")
                    p.have("h_eq: vN_succ (vN m) = Empty").by_rewrite_of(
                        "h", [VN_BASE, VN_STEP]
                    )
                    p.have("h_neq: ~(vN_succ (vN m) = Empty)").by(
                        VN_SUCC_NEQ_ZERO, "vN m"
                    )
                    p.absurd().by_conj("h_neq", "h_eq")
                with p.step("IH_n_unused"):
                    p.assume("h: vN (SUC0 m) = vN (SUC0 n)")
                    p.have("h_succ: vN_succ (vN m) = vN_succ (vN n)").by_rewrite_of(
                        "h", [VN_STEP]
                    )
                    p.have("h_vmn: vN m = vN n").by(
                        VN_SUCC_INJ, "vN m", "vN n", "h_succ"
                    )
                    p.have("h_mn: m = n").by("IH", "n", "h_vmn")
                    p.thus("SUC0 m = SUC0 n").by_cong(SUC0_c, "h_mn")


# ---------------------------------------------------------------------------
# VN_PRED -- predecessor on the image of vN.
#
#   |- !n. ~(vN n = Empty) ==> ?y. vN n = vN_succ y
#
# The sketch's universal-over-hf form (``!x. ~(x = Empty) ==> ?y.
# x = vN_succ y``) is not provable: ``vN_succ`` is not surjective on
# hf (e.g. 2 = {1} is not vN_succ of anything). The image-restricted
# form below is the one godel_first.py actually needs (it case-splits
# on a vN-numeral being zero or a successor) and is a one-step
# induction.
# ---------------------------------------------------------------------------


@proof
def VN_PRED(p):
    p.goal("!n. ~(vN n = Empty) ==> ?y. vN n = vN_succ y")
    p.fix("n")
    with p.induction("n"):
        with p.base():
            p.assume("h: ~(vN 0 = Empty)")
            p.have("h_eq: vN 0 = Empty").by_thm(VN_BASE)
            p.absurd().by_conj("h", "h_eq")
        with p.step("IH_unused"):
            p.assume("h: ~(vN (SUC0 n) = Empty)")
            p.have("h_step: vN (SUC0 n) = vN_succ (vN n)").by(VN_STEP, "n")
            p.thus("?y. vN (SUC0 n) = vN_succ y").by_witness("vN n", "h_step")


# ---------------------------------------------------------------------------
# HF-model interpretation.
#
# The carrier is hf = nat0. Interpretations:
#
#   0_Q  ↦ Empty   ( = 0 : nat0 )
#   S_Q  ↦ SUC0    -- *not* vN_succ; see note below.
#   +_Q  ↦ n0plus
#   *_Q  ↦ n0times
#
# Why not vN_succ? The von Neumann successor on hf is not surjective
# (e.g., {1} is not the vN_successor of any HF set), so Q5's universal
# closure ``!x y. plus(x, vN_succ y) = vN_succ (plus x y)`` over the
# whole carrier cannot be satisfied without elaborate scaffolding
# (predecessor-via-SELECT plus well-founded recursion). Picking SUC0
# instead makes Q4-Q7 immediate Peano facts on nat0 while keeping the
# carrier identical (hf = nat0). The vN/vN_succ machinery above
# remains available for syntax encoding work in godel_first.py.
# ---------------------------------------------------------------------------


# Peano + on nat0 (recursion on the second argument).
N0PLUS_BASE, N0PLUS_STEP = define_recursive_0(
    "n0plus",
    parse_type("nat0 -> nat0 -> nat0"),
    _x_n0,  # carried first arg
    _x_n0,  # base: n0plus x 0 = x
    mk_abs(_n_n0, mk_abs(_a_hf, mk_suc0(_a_hf))),  # step: \k a. SUC0 a
    result_ty=nat0_ty,
)
n0plus = mk_const("n0plus", [])


# Peano * on nat0.
N0TIMES_BASE, N0TIMES_STEP = define_recursive_0(
    "n0times",
    parse_type("nat0 -> nat0 -> nat0"),
    _x_n0,  # carried first arg
    ZERO,  # base: n0times x 0 = 0
    mk_abs(_n_n0, mk_abs(_a_hf, mk_app(n0plus, _a_hf, _x_n0))),  # step: a + x
    result_ty=nat0_ty,
)
n0times = mk_const("n0times", [])


# ---------------------------------------------------------------------------
# Q1: |- !n. ~(SUC0 n = Empty).
# Direct: AXIOM_3_0 modulo EMPTY_DEF.
# ---------------------------------------------------------------------------


@proof
def PEANO_1(p):
    p.goal("!n. ~(SUC0 n = Empty)")
    p.fix("n")
    with p.suppose("h: SUC0 n = Empty"):
        p.have("h_zero: SUC0 n = 0").by_rewrite_of("h", [EMPTY_DEF])
        p.have("h_neq: ~(SUC0 n = 0)").by(AXIOM_3_0, "n")
        p.absurd().by_conj("h_neq", "h_zero")


# ---------------------------------------------------------------------------
# Q2: |- !m n. SUC0 m = SUC0 n ==> m = n.
# Direct: AXIOM_4_0.
# ---------------------------------------------------------------------------


@proof
def PEANO_2(p):
    p.goal("!m n. SUC0 m = SUC0 n ==> m = n")
    p.fix("m n")
    p.assume("h: SUC0 m = SUC0 n")
    p.thus("m = n").by(AXIOM_4_0, "m", "n", "h")


# ---------------------------------------------------------------------------
# Q3: |- !x. ~(x = Empty) ==> ?y. x = SUC0 y.
# Induction on x. Base contradicts the hypothesis; step exhibits the
# predecessor.
# ---------------------------------------------------------------------------


@proof
def PEANO_3(p):
    from fusion import REFL

    p.goal("!x. ~(x = Empty) ==> ?y. x = SUC0 y")
    p.fix("x")
    with p.induction("x"):
        with p.base():
            p.assume("h: ~(0 = Empty)")
            p.have("h_eq: 0 = Empty").by_rewrite([EMPTY_DEF])
            p.absurd().by_conj("h", "h_eq")
        with p.step("IH_unused"):
            p.assume("h: ~(SUC0 x = Empty)")
            p.thus("?y. SUC0 x = SUC0 y").by_witness("x", REFL(mk_suc0(_x_n0)))


# ---------------------------------------------------------------------------
# Q4: |- !x. n0plus x Empty = x.   N0PLUS_BASE under EMPTY_DEF.
# ---------------------------------------------------------------------------


@proof
def PEANO_4(p):
    p.goal("!x. n0plus x Empty = x")
    p.fix("x")
    p.thus("n0plus x Empty = x").by_rewrite([EMPTY_DEF, N0PLUS_BASE])


# ---------------------------------------------------------------------------
# Q5: |- !x y. n0plus x (SUC0 y) = SUC0 (n0plus x y).   N0PLUS_STEP.
# ---------------------------------------------------------------------------


@proof
def PEANO_5(p):
    p.goal("!x y. n0plus x (SUC0 y) = SUC0 (n0plus x y)")
    p.fix("x y")
    p.thus("n0plus x (SUC0 y) = SUC0 (n0plus x y)").by_rewrite([N0PLUS_STEP])


# ---------------------------------------------------------------------------
# Q6: |- !x. n0times x Empty = Empty.   N0TIMES_BASE under EMPTY_DEF.
# ---------------------------------------------------------------------------


@proof
def PEANO_6(p):
    p.goal("!x. n0times x Empty = Empty")
    p.fix("x")
    p.thus("n0times x Empty = Empty").by_rewrite([EMPTY_DEF, N0TIMES_BASE])


# ---------------------------------------------------------------------------
# Q7: |- !x y. n0times x (SUC0 y) = n0plus (n0times x y) x.   N0TIMES_STEP.
# ---------------------------------------------------------------------------


@proof
def PEANO_7(p):
    p.goal("!x y. n0times x (SUC0 y) = n0plus (n0times x y) x")
    p.fix("x y")
    p.thus("n0times x (SUC0 y) = n0plus (n0times x y) x").by_rewrite([N0TIMES_STEP])


# ---------------------------------------------------------------------------
# bi-interpretation, briefly.
# ---------------------------------------------------------------------------
#
# Ackermann's theorem (1937): PA and ZF - Infinity prove the same
# arithmetic sentences. The forward translation is the encoding above
# (every set is a natural number); the reverse is "the natural
# numbers are the von Neumann ordinals" -- which is what Stage 4
# explicitly constructs.
#
# In pyzar this means: any theorem of HF (Stages 1-4 here) is an
# arithmetic theorem of nat0, and conversely any arithmetic theorem
# transports to an HF statement via vN. We do NOT mechanise the
# bi-interpretation as an internal proof translation -- we only need
# its semantic upshot (Stage 4 above). godel_first.py uses neither
# direction explicitly; the bi-interpretation is conceptual scaffolding.

if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 2 OK -- In defined, membership lemmas proved.")
    print("  IN_DEF          :", pp_thm(IN_DEF))
    print("  IN_AT           :", pp_thm(IN_AT))
    print("  IN_ZERO         :", pp_thm(IN_ZERO))
    print("  IN_LT           :", pp_thm(IN_LT))
    print("  IN_EXT          :", pp_thm(IN_EXT))
    print("Stage 3 partial -- Empty/Insert defined.")
    print("  EMPTY_DEF       :", pp_thm(EMPTY_DEF))
    print("  NOT_IN_EMPTY    :", pp_thm(NOT_IN_EMPTY))
    print("  INSERT_DEF      :", pp_thm(INSERT_DEF))
    print("  INSERT_AT       :", pp_thm(INSERT_AT))
    print("  IN_INSERT_SAME  :", pp_thm(IN_INSERT_SAME))
    print("  IN_INSERT_DIFF  :", pp_thm(IN_INSERT_DIFF))
    print("  SINGLETON_DEF   :", pp_thm(SINGLETON_DEF))
    print("  SINGLETON_AT    :", pp_thm(SINGLETON_AT))
    print("  IN_SINGLETON    :", pp_thm(IN_SINGLETON))
    print("  PAIR_DEF        :", pp_thm(PAIR_DEF))
    print("  PAIR_AT         :", pp_thm(PAIR_AT))
    print("  IN_PAIR         :", pp_thm(IN_PAIR))
    print("  PAIR_ORD_DEF    :", pp_thm(PAIR_ORD_DEF))
    print("  PAIR_ORD_AT     :", pp_thm(PAIR_ORD_AT))
    print("  IN_PAIR_ORD     :", pp_thm(IN_PAIR_ORD))
    print("Stage 3 (cont.) -- Union (bit-OR on HF sets).")
    print("  UNION_DEF       :", pp_thm(UNION_DEF))
    print("  UNION_AT_ZERO   :", pp_thm(UNION_AT_ZERO))
    print("  UNION_AT_NZ     :", pp_thm(UNION_AT_NZ))
    print("  UNION_HALF      :", pp_thm(UNION_HALF))
    print("  UNION_ODD       :", pp_thm(UNION_ODD))
    print("  IN_SUCC_AT      :", pp_thm(IN_SUCC_AT))
    print("  IN_UNION        :", pp_thm(IN_UNION))
    print("Stage 4 -- vN embedding lemmas (canonical von Neumann).")
    print("  VN_SUCC_DEF     :", pp_thm(VN_SUCC_DEF))
    print("  VN_SUCC_AT      :", pp_thm(VN_SUCC_AT))
    print("  VN_SUCC_NEQ_ZERO:", pp_thm(VN_SUCC_NEQ_ZERO))
    print("  VN_BASE         :", pp_thm(VN_BASE))
    print("  VN_STEP         :", pp_thm(VN_STEP))
    print("  VN_SUCC_INJ     :", pp_thm(VN_SUCC_INJ))
    print("  VN_INJ          :", pp_thm(VN_INJ))
    print("  VN_PRED         :", pp_thm(VN_PRED))
    print("Stage 4 -- HF-axiom lemmas in the HF model.")
    print("  N0PLUS_BASE     :", pp_thm(N0PLUS_BASE))
    print("  N0PLUS_STEP     :", pp_thm(N0PLUS_STEP))
    print("  N0TIMES_BASE    :", pp_thm(N0TIMES_BASE))
    print("  N0TIMES_STEP    :", pp_thm(N0TIMES_STEP))
    print("  PEANO_1           :", pp_thm(PEANO_1))
    print("  PEANO_2           :", pp_thm(PEANO_2))
    print("  PEANO_3           :", pp_thm(PEANO_3))
    print("  PEANO_4           :", pp_thm(PEANO_4))
    print("  PEANO_5           :", pp_thm(PEANO_5))
    print("  PEANO_6           :", pp_thm(PEANO_6))
    print("  PEANO_7           :", pp_thm(PEANO_7))
