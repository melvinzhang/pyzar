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

# ---------------------------------------------------------------------------
# Implementation roadmap (revised against godel_first.py)
# ---------------------------------------------------------------------------
#
# Prerequisites: bits.py (DONE), nat0_order.py (DONE), parts of nat.py
# (+, *, < on nat0; the additive/multiplicative parts already exist
# from the rationals-construction work).
#
#   1. Stage 2: hf alias + In definition. ~10 lines, no proof work.
#
#   2. Stage 3: Empty, Insert, Singleton, Pair, Pair_ord, Union,
#      plus the Foundation derived rule. ~150 lines.
#      Pair_ord and Union are the only new substance; the rest are
#      one-step renames of bits.py lemmas.
#
#   3. Stage 4: vN, vN_succ, vN_plus, vN_times, plus the eight
#      Q-axiom lemmas. ~150 lines.
#
#   Total here: ~310 lines. (Down from ~350 in the original sketch
#   thanks to dropping Pow / Repl / Sep / refutation-of-Infinity.)
#
# Comparison: the original sketch was ~500 lines aimed at full ZF
# surface. The trim above sheds roughly 40% of that scope. If a
# downstream consumer turns up wanting Pow / Repl / Sep, restore them
# in a sibling ``hf_zf.py`` rather than enlarging this file -- the
# Q-model construction stays cleanest when not entangled with the
# generic constructors.
#
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
# Membership lemmas reduce to the bit lemmas already in bits.py:
#
#   |- ~In x Empty                                from BIT_AT_ZERO
#   |- !x y. In x y ==> nat0_lt x y               from BIT_LT  (foundation core)
#   |- !a b. (!x. In x a = In x b) ==> a = b      from BIT_EXTENSIONALITY
#                                                 (extensionality, immediate)
#
# No proof needed beyond a definitional unfolding step. ~30 lines.


from fusion import Var
from basics import mk_const, rand
from parser import define, parse_type
from nat0 import nat0_ty, ZERO
from bits import BIT_AT_ZERO, BIT_LT, BIT_EXTENSIONALITY
from nat0_order import nat0_lt  # noqa: F401  -- parser alias, used in goals
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
# What godel_first.py uses from this stage:
#   (a) Empty, Insert, Singleton, Pair        -- to encode Q syntax as
#                                                 finite tuples (HF trees).
#   (b) Pair_ord (ordered Kuratowski pair)    -- to encode (index, value)
#                                                 entries inside a tuple.
#   (c) Union                                 -- to define the von Neumann
#                                                 successor in the model
#                                                 of Q (Stage 6 below).
#   (d) Foundation as a derived rule          -- to argue that the
#                                                 minimum-bit element
#                                                 of any nonempty HF set
#                                                 has no member also in it.
#                                                 Drops out of BIT_LT.
#
# What godel_first.py does NOT use, and is therefore deferred:
#   * Pow, Repl, Sep  -- the general ZF constructors. Doable in HF
#     (sketches in the original draft of this file); they are not
#     called from anywhere in the godel_first chain. Punt to a future
#     ``hf_zf.py`` if/when a consumer wants full ZF surface.
#   * Refutation of Infinity. A nice theorem, also deferred -- the
#     consistency-of-Q argument in godel_first.py uses the *positive*
#     fact that HF models Q, not the negative fact that HF refutes
#     Infinity.
# ---------------------------------------------------------------------------

# EMPTY  -- numeric 0.
#   defn:  Empty := 0
#   thm:   |- !x. ~In x Empty
#   proof: BIT_AT_ZERO.

# INSERT i s -- add element i.
#   defn:  Insert i s := set_bit i s
#   thms:  |- !i s. In i (Insert i s) = T                  (BIT_AT_SET_BIT_SAME)
#          |- !i j s. ~(i = j) ==> In j (Insert i s) = In j s
#                                                          (BIT_AT_SET_BIT_DIFF)
#   note:  no proof work -- both lemmas are direct renames.

# SINGLETON x -- {x}.
#   defn:  Singleton x := Insert x Empty   = pow2 x
#   thm:   |- !x y. In y (Singleton x) = (y = x)
#   proof: BIT_AT_POW2_SAME / BIT_AT_POW2_DIFF + EXCLUDED_MIDDLE.
#          ~10 lines.

# PAIR x y -- {x, y}  (unordered).
#   defn:  Pair x y := Insert x (Singleton y)
#   thm:   |- !a b z. In z (Pair a b) = (z = a \\/ z = b)   (PAIRING)
#   proof: case-split on z=a; INSERT lemmas + SINGLETON. ~15 lines.

# PAIR_ORD x y -- Kuratowski (x, y) := {{x}, {x, y}}.
#   defn:  Pair_ord x y := Pair (Singleton x) (Pair x y)
#   thm:   |- !a b c d. Pair_ord a b = Pair_ord c d
#                       <=> (a = c /\\ b = d)              (ordered-pair char.)
#   proof: forward direction by EXTENSIONALITY: equal sets share their
#          singleton coordinate, hence a = c; the {a,b} = {c,d} clause
#          then pins b = d once a = c. Reverse direction immediate.
#          ~30 lines, the only mildly substantive lemma in Stage 3.

# UNION y -- bitwise OR of bits of members of y.
#   defn:  Union y := OR_below (SUC0 y)
#                              (\i. COND (bit i y) (rep_member i) 0)
#          where rep_member i = i  (the HF member at bit position i).
#          Concretely: bit x (Union y) = T  iff
#                      ?i. bit i y /\\ bit x i.
#          Implementation: recursion on a numeric "scan bound";
#          BIT_LT gives ``~(bit i y) for i >= y``, so ``SUC0 y`` is a
#          safe upper bound.
#   thm:   |- !y x. In x (Union y) = ?z. In x z /\\ In z y     (UNION)
#   proof: bit-extensionality + the OR_below characterisation lemma.
#          ~50 lines including the OR_below scaffolding.

# FOUNDATION (as a derived rule, not a constructor).
#   thm:   |- !a. (?x. In x a) ==>
#                 ?x. In x a /\\ ~(?y. In y a /\\ In y x)
#   proof: ``In`` strictly decreases the numeric value (BIT_LT).
#          So given any non-empty ``a``, the numerically-smallest
#          element x of ``In . a`` (well-ordering of nat0) has
#          no member also in ``a`` -- any such y would be smaller
#          still, contradicting minimality.
#          ~25 lines once nat0 well-ordering is invoked.
#   note:  this is the slickest payoff of the encoding -- foundation
#          becomes the well-ordering of the natural numbers.

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
# Define the von Neumann numerals as a HOL function vN : nat0 -> hf:
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
# We pick the ``Insert x x`` form to keep proofs short:
#
#   thm:   |- !n. vN_succ (vN n) = set_bit (vN n) (vN n)
#                                                    (definition unfold)
#
# The four lemmas godel_first.py Stage 6 actually consumes, with
# their proof sketches:
#
#   VN_SUCC_NEQ_ZERO  :  |- !n. ~(vN_succ (vN n) = Empty)
#     Proof: vN_succ x = set_bit x x, which has bit x set
#            (BIT_AT_SET_BIT_SAME), but bit x 0 = F (BIT_AT_ZERO).
#            So vN_succ x != 0 = Empty.    ~10 lines.
#
#   VN_SUCC_INJ        :  |- !m n. vN_succ m = vN_succ n ==> m = n
#     Proof: from set_bit m m = set_bit n n, take HALF on both sides:
#            vN_succ x peels exactly one bit at position x, so HALF
#            recovers x in each case... actually cleaner: bit x of
#            set_bit m m is "T iff x = m \\/ bit x m". The maximum
#            bit position of set_bit m m is therefore max(m, max-bit(m))
#            = m (because BIT_LT gives every set bit of m below m,
#            but bit m itself is set). So m = n via the maximum-bit
#            characterisation. ~40 lines, the bulk being the
#            "maximum bit position" lemma. (Alternative shortcut:
#            argue via cardinality / bit-extensionality directly;
#            comparable length.)
#
#   VN_PRED            :  |- !x. ~(x = Empty) ==> ?y. x = vN_succ y
#     Stated WITHIN the image of vN: i.e. only required when x is
#     itself a vN numeral. This is what Q3 needs in the model.
#     Proof: case-split on x = vN 0 (impossible by hypothesis) vs
#            x = vN (S k); the latter directly gives y := vN k.
#            ~15 lines plus a vN-image case-analysis lemma
#            (provable by cases_on EXCLUDED_MIDDLE on x = vN 0,
#            then nat0 induction extracting the predecessor).
#
#   VN_INJ             :  |- !m n. vN m = vN n ==> m = n
#     The embedding is injective. Used to bridge HOL equality on
#     numerals and Q-internal equality. Proof: nat0 induction on
#     m with case-split on n; VN_SUCC_NEQ_ZERO + VN_SUCC_INJ.
#     ~25 lines.
#
# Arithmetic on vN-numerals (Q4-Q7):
#
#   defn:  vN_plus  x y := vN ((rep x) + (rep y))      via VN_INJ
#          vN_times x y := vN ((rep x) * (rep y))
#     where ``rep`` is the (HOL-level, total but only canonical on
#     the vN image) inverse of vN. We do NOT need ``rep`` to be
#     definable in the object language Q -- it is a HOL convenience
#     used to *define* vN_plus / vN_times as functions on hf, then
#     the Q-axiom proofs reduce to nat0-arithmetic identities.
#
#   thm:   VN_PLUS_ZERO   : |- !x. vN_plus x (vN 0)     = x
#          VN_PLUS_SUCC   : |- !x y. vN_plus x (vN_succ y) = vN_succ (vN_plus x y)
#          VN_TIMES_ZERO  : |- !x. vN_times x (vN 0)    = vN 0
#          VN_TIMES_SUCC  : |- !x y. vN_times x (vN_succ y) = vN_plus (vN_times x y) x
#     Each is one nat0-arithmetic line plus VN_INJ to translate.
#     ~10 lines apiece, ~50 total.
#
# Bundle: Q1 -> VN_SUCC_NEQ_ZERO; Q2 -> VN_SUCC_INJ; Q3 -> VN_PRED;
#         Q4-Q7 -> VN_PLUS_*, VN_TIMES_*. Together they give the
#         "HF |= Q" theorem godel_first.py Stage 6 imports.
#
# Total Stage 4: ~150 lines (definitions + 4 + 4 named lemmas).



# ---------------------------------------------------------------------------
# Stage 5 -- bi-interpretation, briefly.
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
