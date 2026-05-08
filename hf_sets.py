"""Hereditarily finite sets via Ackermann's bit-encoding.

SKETCH ONLY -- this file lays out the construction; the proofs are
stubbed with strategy comments rather than executed. Scope is set by
the immediate downstream consumer ``godel_first.py``: we build only as
much HF as it needs (encoding for the syntax of Q + a model of Q).
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
#                         function (HOL-level, not Q-internal),
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
    SUC0,
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

    th_x = AP_THM(IN_DEF, _x_n0)                 # |- In x = (\x. \y. bit x y) x
    th_x_eq = TRANS(th_x, BETA_CONV(rand(th_x._concl)))
    th_xy = AP_THM(th_x_eq, _y_n0)               # |- In x y = (\y. bit x y) y
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
# encoding Q syntax as HF trees: Empty, Insert, Singleton, Pair, and
# the ordered Kuratowski pair Pair_ord (for (index, value) tuple entries).
# Stage 4's Q-model construction sits on top of Insert (vN_succ x =
# Insert x x) and does not need Union, Pow, Repl, Sep, or a derived
# Foundation rule. Each is therefore deferred:
#
#   * Union  -- the original draft used it to define vN_succ as
#               ``Union (Pair x (Singleton x))``. We pick the
#               equivalent ``Insert x x`` form instead (one bit-flip,
#               no recursion-over-bit-positions scaffolding).
#   * Pow, Repl, Sep  -- general ZF constructors; defer to a future
#               ``hf_zf.py`` if a consumer wants full ZF surface.
#   * Foundation as a derived rule -- a one-liner via BIT_LT + nat0
#               well-ordering, but unused by godel_first.py (the
#               Q-consistency argument needs the positive fact that
#               HF models Q, not Foundation).
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
#                 is *not* proved here -- godel_first.py Stage 1 gets
#                 the injectivity it needs from bit-extensionality at
#                 the nat0 level, never from the structural form. The
#                 standard ~80-line case-analysis proof is left as a
#                 TODO and recorded in the comment immediately preceding
#                 the deferral marker further down.
# ---------------------------------------------------------------------------

from bits import (
    BIT_AT_SET_BIT_SAME,
    BIT_AT_SET_BIT_DIFF,
    BIT_AT_POW2_SAME,
    BIT_AT_POW2_DIFF,
)


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
    p.thus("In i (Insert i s) = T").by_rewrite(
        [IN_AT, INSERT_AT, BIT_AT_SET_BIT_SAME]
    )


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
            p.thus("In y (Singleton x) = (y = x)").by_rewrite(
                ["h_lhs", "h_rhs"]
            )
        with p.case("hnyx: ~(y = x)"):
            p.have("hb: bit y (pow2 x) = F").by(
                BIT_AT_POW2_DIFF, "x", "y", "hnyx"
            )
            p.have("h_lhs: In y (Singleton x) = F").by_rewrite_of(
                "hb", [IN_AT, SINGLETON_AT]
            )
            p.have("h_rhs: (y = x) = F").by_thm(EQF_INTRO(p.fact("hnyx")))
            p.thus("In y (Singleton x) = (y = x)").by_rewrite(
                ["h_lhs", "h_rhs"]
            )


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
            p.have("h_rhs: (z = a \\/ z = b) = T").by_thm(
                EQT_INTRO(p.fact("h_disj"))
            )
            p.thus("In z (Pair a b) = (z = a \\/ z = b)").by_rewrite(
                ["h_lhs", "h_rhs"]
            )
        with p.case("hnza: ~(z = a)"):
            # IN_INSERT_DIFF needs ~(a = z); flip ~(z = a).
            with p.have("h_az: ~(a = z)").proof():
                with p.suppose("haz: a = z"):
                    p.have("hza2: z = a").by_thm(SYM(p.fact("haz")))
                    p.absurd().by_conj("hnza", "hza2")
            p.have(
                "h_diff: In z (Insert a (Singleton b)) = In z (Singleton b)"
            ).by(IN_INSERT_DIFF, "a", "z", "Singleton b", "h_az")
            p.have("h_sing: In z (Singleton b) = (z = b)").by(
                IN_SINGLETON, "b", "z"
            )
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
            p.thus("In z (Pair a b) = (z = a \\/ z = b)").by_rewrite(
                ["h_lhs", "h_rhs"]
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
    p.have("h: In z (Pair (Singleton a) (Pair a b)) "
           "= (z = Singleton a \\/ z = Pair a b)").by(
        IN_PAIR, "Singleton a", "Pair a b", "z"
    )
    p.thus(
        "In z (Pair_ord a b) = (z = Singleton a \\/ z = Pair a b)"
    ).by_rewrite_of("h", [PAIR_ORD_AT])


# ---------------------------------------------------------------------------
# DEFERRED: |- !a b c d. (Pair_ord a b = Pair_ord c d) = (a = c /\ b = d).
#
# The standard Kuratowski-pair injectivity theorem. Proved from
# IN_PAIR_ORD + IN_EXT + IN_SINGLETON + IN_PAIR by case analysis on the
# four set-equalities one extracts. Unrolls to ~80-120 lines in the DSL.
# Not required by the immediate godel_first.py encoding (which gets
# injectivity for free from bit-extensionality at the nat0 level), so
# we leave it as a TODO and revisit if a downstream caller actually
# needs the structural form.
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Stage 4 -- a model of Q inside HF.   (used by godel_first.py Stage 6)
# ---------------------------------------------------------------------------
#
# This is the *only* substantive client of Stage 3 from
# godel_first.py: the model construction that discharges the
# consistency assumption.
#
# We split Stage 4 into two pieces:
#
#   (a) The canonical von Neumann embedding vN : nat0 -> hf, with
#       its successor and the injectivity / nonzeroness lemmas. This
#       is the "right" embedding of N into HF and is independently
#       useful for syntax-encoding work in godel_first.py Stage 1
#       (every numeral has a canonical HF representation).
#
#   (b) The Q-model interpretation. Carrier = hf = nat0; the symbols
#       are 0 ↦ Empty, S ↦ SUC0, + ↦ n0plus, * ↦ n0times. Q1-Q7
#       reduce to Peano facts on nat0. See the design note below.
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
# ---------- (b) The Q-model interpretation ----------
#
# Design note (deviation from the original sketch). The original sketch
# proposed interpreting Q's S as ``vN_succ`` and defining
# ``vN_plus x y := vN ((rep x) + (rep y))`` via a partial inverse
# ``rep`` of vN. Two problems with that path:
#
#   1. Q4's universal closure ``!x. plus(x, 0) = x`` becomes
#      ``vN(rep x) = x``, which holds only on the image of vN.
#   2. Q5's universal closure refers to ``vN_succ y`` for arbitrary
#      y:hf, so vN_plus must be definable for all y; outside the image
#      of vN_succ (which is most of hf), satisfying Q5 needs a
#      well-founded predecessor extraction (SELECT + recursion).
#
# Both go away by picking SUC0 instead of vN_succ as the model's
# successor. The carrier is unchanged (hf = nat0), so HF still "supplies
# the model" in the godel_first.py Stage 6 sense, and Q4-Q7 become
# direct Peano equations:
#
#   defn:  n0plus  : nat0 -> nat0 -> nat0   (Peano + on nat0)
#          n0times : nat0 -> nat0 -> nat0   (Peano * on nat0)
#     defined via define_recursive_0 by recursion on the second arg.
#
#   thm:   Q1_HF :  |- !n.   ~(SUC0 n = Empty)
#          Q2_HF :  |- !m n. SUC0 m = SUC0 n ==> m = n
#          Q3_HF :  |- !x.   ~(x = Empty) ==> ?y. x = SUC0 y
#          Q4_HF :  |- !x.   n0plus x Empty = x
#          Q5_HF :  |- !x y. n0plus x (SUC0 y) = SUC0 (n0plus x y)
#          Q6_HF :  |- !x.   n0times x Empty = Empty
#          Q7_HF :  |- !x y. n0times x (SUC0 y) = n0plus (n0times x y) x
#
#     Q1 reduces to AXIOM_3_0 modulo EMPTY_DEF; Q2 is AXIOM_4_0
#     verbatim; Q3 is one nat0 induction; Q4-Q7 are the BASE/STEP
#     theorems returned by define_recursive_0 modulo EMPTY_DEF.
#     ~50 lines total for the seven lemmas + the two recursive
#     definitions.
#
# The vN/vN_succ block above remains in the file because godel_first.py
# Stage 1 wants the canonical vN embedding for syntax encoding (each
# numeral that appears inside a Q-formula gets a definite HF code via
# vN). It is *not* used as the Q-model's successor.

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
        p.have("hT: In x (vN_succ x) = T").by_rewrite(
            [VN_SUCC_AT, IN_INSERT_SAME]
        )
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
            p.have("h_bm: bit m (set_bit m m) = T").by(
                BIT_AT_SET_BIT_SAME, "m", "m"
            )
            p.have("h_bm_n: bit m (set_bit n n) = T").by_rewrite_of(
                "h_bm", ["h_set"]
            )
            p.have("h_diff_n: bit m (set_bit n n) = bit m n").by(
                BIT_AT_SET_BIT_DIFF, "n", "m", "n", "h_nm"
            )
            p.have("h_bit_mn: bit m n = T").by_rewrite_of(
                "h_bm_n", ["h_diff_n"]
            )
            p.have("h_bmn_pos: bit m n").by_thm(EQT_ELIM(p.fact("h_bit_mn")))
            p.have("h_lt_mn: nat0_lt m n").by(BIT_LT, "n", "m", "h_bmn_pos")
            # Direction 2 (symmetric).
            p.have("h_bn: bit n (set_bit n n) = T").by(
                BIT_AT_SET_BIT_SAME, "n", "n"
            )
            p.have("h_set_sym: set_bit n n = set_bit m m").by_thm(
                SYM(p.fact("h_set"))
            )
            p.have("h_bn_m: bit n (set_bit m m) = T").by_rewrite_of(
                "h_bn", ["h_set_sym"]
            )
            p.have("h_diff_m: bit n (set_bit m m) = bit n m").by(
                BIT_AT_SET_BIT_DIFF, "m", "n", "m", "hnmn"
            )
            p.have("h_bit_nm: bit n m = T").by_rewrite_of(
                "h_bn_m", ["h_diff_m"]
            )
            p.have("h_bnm_pos: bit n m").by_thm(EQT_ELIM(p.fact("h_bit_nm")))
            p.have("h_lt_nm: nat0_lt n m").by(BIT_LT, "m", "n", "h_bnm_pos")
            # Asymmetry contradiction.
            p.have("h_nasym: ~(nat0_lt n m)").by(
                NAT0_LT_ASYM, "m", "n", "h_lt_mn"
            )
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
                    p.have("h_sym: vN_succ (vN n) = Empty").by_thm(
                        SYM(p.fact("h_eq"))
                    )
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
# Q-model interpretation.
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
    _x_n0,            # carried first arg
    _x_n0,            # base: n0plus x 0 = x
    mk_abs(_n_n0, mk_abs(_a_hf, mk_suc0(_a_hf))),  # step: \k a. SUC0 a
    result_ty=nat0_ty,
)
n0plus = mk_const("n0plus", [])


# Peano * on nat0.
N0TIMES_BASE, N0TIMES_STEP = define_recursive_0(
    "n0times",
    parse_type("nat0 -> nat0 -> nat0"),
    _x_n0,            # carried first arg
    ZERO,             # base: n0times x 0 = 0
    mk_abs(_n_n0, mk_abs(_a_hf, mk_app(n0plus, _a_hf, _x_n0))),  # step: a + x
    result_ty=nat0_ty,
)
n0times = mk_const("n0times", [])


# ---------------------------------------------------------------------------
# Q1: |- !n. ~(SUC0 n = Empty).
# Direct: AXIOM_3_0 modulo EMPTY_DEF.
# ---------------------------------------------------------------------------


@proof
def Q1_HF(p):
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
def Q2_HF(p):
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
def Q3_HF(p):
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
def Q4_HF(p):
    p.goal("!x. n0plus x Empty = x")
    p.fix("x")
    p.thus("n0plus x Empty = x").by_rewrite([EMPTY_DEF, N0PLUS_BASE])


# ---------------------------------------------------------------------------
# Q5: |- !x y. n0plus x (SUC0 y) = SUC0 (n0plus x y).   N0PLUS_STEP.
# ---------------------------------------------------------------------------


@proof
def Q5_HF(p):
    p.goal("!x y. n0plus x (SUC0 y) = SUC0 (n0plus x y)")
    p.fix("x y")
    p.thus("n0plus x (SUC0 y) = SUC0 (n0plus x y)").by_rewrite([N0PLUS_STEP])


# ---------------------------------------------------------------------------
# Q6: |- !x. n0times x Empty = Empty.   N0TIMES_BASE under EMPTY_DEF.
# ---------------------------------------------------------------------------


@proof
def Q6_HF(p):
    p.goal("!x. n0times x Empty = Empty")
    p.fix("x")
    p.thus("n0times x Empty = Empty").by_rewrite([EMPTY_DEF, N0TIMES_BASE])


# ---------------------------------------------------------------------------
# Q7: |- !x y. n0times x (SUC0 y) = n0plus (n0times x y) x.   N0TIMES_STEP.
# ---------------------------------------------------------------------------


@proof
def Q7_HF(p):
    p.goal("!x y. n0times x (SUC0 y) = n0plus (n0times x y) x")
    p.fix("x y")
    p.thus("n0times x (SUC0 y) = n0plus (n0times x y) x").by_rewrite(
        [N0TIMES_STEP]
    )

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
    print("Stage 4 -- vN embedding lemmas (canonical von Neumann).")
    print("  VN_SUCC_DEF     :", pp_thm(VN_SUCC_DEF))
    print("  VN_SUCC_AT      :", pp_thm(VN_SUCC_AT))
    print("  VN_SUCC_NEQ_ZERO:", pp_thm(VN_SUCC_NEQ_ZERO))
    print("  VN_BASE         :", pp_thm(VN_BASE))
    print("  VN_STEP         :", pp_thm(VN_STEP))
    print("  VN_SUCC_INJ     :", pp_thm(VN_SUCC_INJ))
    print("  VN_INJ          :", pp_thm(VN_INJ))
    print("  VN_PRED         :", pp_thm(VN_PRED))
    print("Stage 4 -- Q-axiom lemmas in the HF model.")
    print("  N0PLUS_BASE     :", pp_thm(N0PLUS_BASE))
    print("  N0PLUS_STEP     :", pp_thm(N0PLUS_STEP))
    print("  N0TIMES_BASE    :", pp_thm(N0TIMES_BASE))
    print("  N0TIMES_STEP    :", pp_thm(N0TIMES_STEP))
    print("  Q1_HF           :", pp_thm(Q1_HF))
    print("  Q2_HF           :", pp_thm(Q2_HF))
    print("  Q3_HF           :", pp_thm(Q3_HF))
    print("  Q4_HF           :", pp_thm(Q4_HF))
    print("  Q5_HF           :", pp_thm(Q5_HF))
    print("  Q6_HF           :", pp_thm(Q6_HF))
    print("  Q7_HF           :", pp_thm(Q7_HF))
