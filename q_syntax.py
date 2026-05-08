r"""Syntax of Robinson's Q encoded as nat0 (Stage 1 of ``godel_first.py``).

Per the implementation roadmap in ``godel_first.py``:

    1. ``q_syntax.py`` -- term and formula datatypes (encoded as nat0
       via the Kuratowski ordered-pair primitive ``Pair_ord``); Goedel
       numbering; substitution; unique readability; free-variable
       analysis. ~300 lines.

------------------------------------------------------------------
Encoding (option 2: flat pairing)
------------------------------------------------------------------

Q's signature: 0, S, +, *, =, plus first-order connectives and
quantifiers. We pick an inductive grammar:

    Term  ::=  Zero | Succ Term | Var num | Plus Term Term | Times Term Term
    Form  ::=  Eq Term Term | Not Form | Imp Form Form | Forall num Form

The encoding flattens each constructor onto ``Pair_ord`` from
``hf_sets.py`` (the Kuratowski ordered pair, which is itself a nat0):

    Zero_t            :=  0
    Succ_t t          :=  Pair_ord 1 t
    Var_t  v          :=  Pair_ord 2 v
    Plus_t  t1 t2     :=  Pair_ord 3 (Pair_ord t1 t2)
    Times_t t1 t2     :=  Pair_ord 4 (Pair_ord t1 t2)
    Eq_f    t1 t2     :=  Pair_ord 5 (Pair_ord t1 t2)
    Not_f   F         :=  Pair_ord 6 F
    Imp_f   F1 F2     :=  Pair_ord 7 (Pair_ord F1 F2)
    Forall_f n F      :=  Pair_ord 8 (Pair_ord n F)

Tags 0-8 are distinct nat0 numerals; arity-2 constructors curry their
two arguments through a second ``Pair_ord``. The encoding is strictly
shallower than a "tagged tuple" HF-set encoding (one or two
``Pair_ord`` layers vs. a ``Pair`` of ``Pair_ord (slot, value)``
entries), which keeps Stage 1's structural lemmas short.

Two universal lemmas drive everything below:

  * ``PAIR_ORD_INJ``       (``hf_sets.py``)
        |- !a b c d. Pair_ord a b = Pair_ord c d ==> (a = c /\ b = d).
  * ``NAT0_LT_PAIR_ORD_L`` / ``NAT0_LT_PAIR_ORD_R``  (``hf_sets.py``)
        |- !a b. nat0_lt a (Pair_ord a b)
        |- !a b. nat0_lt b (Pair_ord a b).

Constructor injectivity (e.g. ``Succ_t a = Succ_t b ==> a = b``)
unfolds to one or two applications of PAIR_ORD_INJ; size lemmas
(e.g. ``nat0_lt t (Succ_t t)``) are one or two applications of the
NAT0_LT_PAIR_ORD pair, chained via ``NAT0_LT_TRANS``. Disjointness
between distinct constructors follows from PAIR_ORD_INJ at slot 0
and tag-numeral inequalities (``~(SUC0 (SUC0 0) = SUC0 0)`` etc.).

``godelnum`` is the identity function on the encoded representation
(``hf_ty = nat0_ty``, no nominal subtype, so the encoded constructor
output IS its own Goedel number).
"""

# ---------------------------------------------------------------------------
# Imports.
# ---------------------------------------------------------------------------

from fusion import Var
from basics import mk_const
from parser import define, parse_type
from nat0 import nat0_ty
from hf_sets import (  # noqa: F401  -- parser aliases for Pair_ord
    Pair_ord,
    PAIR_ORD_INJ,
    NAT0_LT_PAIR_ORD_L,
    NAT0_LT_PAIR_ORD_R,
    IN_PAIR_ORD,
    IN_ZERO,
)
from nat0 import AXIOM_3_0, AXIOM_4_0
from nat0_order import NAT0_LT_TRANS
from proof import proof


_n_n0 = Var("n", nat0_ty)
_t_n0 = Var("t", nat0_ty)
_t1_n0 = Var("t1", nat0_ty)
_t2_n0 = Var("t2", nat0_ty)
_v_n0 = Var("v", nat0_ty)
_phi_n0 = Var("phi", nat0_ty)
_phi1_n0 = Var("phi1", nat0_ty)
_phi2_n0 = Var("phi2", nat0_ty)


# ---------------------------------------------------------------------------
# Term constructors.
#
# Each constructor wraps its arguments in one or two ``Pair_ord`` layers
# with a unique tag at slot 0. Tags are nat0 numerals 0..8 written as
# SUC0 chains so they normalise to closed numerical values.
# ---------------------------------------------------------------------------

ZERO_T_DEF = define("Zero_t", parse_type("nat0"), "0")
Zero_t = mk_const("Zero_t", [])

SUCC_T_DEF = define(
    "Succ_t",
    parse_type("nat0 -> nat0"),
    "\\t:nat0. Pair_ord (SUC0 0) t",
)
Succ_t = mk_const("Succ_t", [])

VAR_T_DEF = define(
    "Var_t",
    parse_type("nat0 -> nat0"),
    "\\v:nat0. Pair_ord (SUC0 (SUC0 0)) v",
)
Var_t = mk_const("Var_t", [])

PLUS_T_DEF = define(
    "Plus_t",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\t1:nat0. \\t2:nat0. "
    "Pair_ord (SUC0 (SUC0 (SUC0 0))) (Pair_ord t1 t2)",
)
Plus_t = mk_const("Plus_t", [])

TIMES_T_DEF = define(
    "Times_t",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\t1:nat0. \\t2:nat0. "
    "Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 0)))) (Pair_ord t1 t2)",
)
Times_t = mk_const("Times_t", [])


# ---------------------------------------------------------------------------
# Form constructors.
# ---------------------------------------------------------------------------

EQ_F_DEF = define(
    "Eq_f",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\t1:nat0. \\t2:nat0. "
    "Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))) (Pair_ord t1 t2)",
)
Eq_f = mk_const("Eq_f", [])

NOT_F_DEF = define(
    "Not_f",
    parse_type("nat0 -> nat0"),
    "\\phi:nat0. Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))) phi",
)
Not_f = mk_const("Not_f", [])

IMP_F_DEF = define(
    "Imp_f",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\phi1:nat0. \\phi2:nat0. "
    "Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))))) "
    "(Pair_ord phi1 phi2)",
)
Imp_f = mk_const("Imp_f", [])

FORALL_F_DEF = define(
    "Forall_f",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\n:nat0. \\phi:nat0. "
    "Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))))) "
    "(Pair_ord n phi)",
)
Forall_f = mk_const("Forall_f", [])


# ---------------------------------------------------------------------------
# Pointwise unfold helpers.  ``define`` returns ``name = \\args. body``;
# we beta-reduce on each argument to get the applied form
# ``name a1 .. ak = body[a1, .., ak]`` so downstream rewrites can
# pattern-match the head.
# ---------------------------------------------------------------------------


def _at1(def_th, x):
    from tactics import AP_THM, BETA_CONV, TRANS, GEN
    from basics import rand
    th = AP_THM(def_th, x)
    th = TRANS(th, BETA_CONV(rand(th._concl)))
    return GEN(x, th)


def _at2(def_th, x, y):
    from tactics import AP_THM, BETA_CONV, TRANS, GENL
    from basics import rand
    th_x = AP_THM(def_th, x)
    th_x = TRANS(th_x, BETA_CONV(rand(th_x._concl)))
    th_xy = AP_THM(th_x, y)
    th_xy = TRANS(th_xy, BETA_CONV(rand(th_xy._concl)))
    return GENL([x, y], th_xy)


SUCC_T_AT = _at1(SUCC_T_DEF, _t_n0)
VAR_T_AT = _at1(VAR_T_DEF, _v_n0)
PLUS_T_AT = _at2(PLUS_T_DEF, _t1_n0, _t2_n0)
TIMES_T_AT = _at2(TIMES_T_DEF, _t1_n0, _t2_n0)
EQ_F_AT = _at2(EQ_F_DEF, _t1_n0, _t2_n0)
NOT_F_AT = _at1(NOT_F_DEF, _phi_n0)
IMP_F_AT = _at2(IMP_F_DEF, _phi1_n0, _phi2_n0)
FORALL_F_AT = _at2(FORALL_F_DEF, _n_n0, _phi_n0)


# ---------------------------------------------------------------------------
# godelnum -- the encoded HF tree IS its own Goedel number. With
# ``hf_ty = nat0_ty`` (no nominal subtype) and the Pair_ord-based
# encoding above, every constructor output is a bona fide nat0, so
# the Goedel-numbering function is the identity.
# ---------------------------------------------------------------------------

GODELNUM_DEF = define(
    "godelnum",
    parse_type("nat0 -> nat0"),
    "\\n:nat0. n",
)
godelnum = mk_const("godelnum", [])


# Pointwise:  |- !n. godelnum n = n.
@proof
def GODELNUM_AT(p):
    p.goal("!n. godelnum n = n")
    p.fix("n")
    p.thus("godelnum n = n").by_thm(p.unfold(GODELNUM_DEF, "n"))


# ---------------------------------------------------------------------------
# Stage 1 (a):  |- !t1 t2. godelnum t1 = godelnum t2 ==> t1 = t2.
# godelnum is the identity, so injectivity collapses to reflexive
# transport across GODELNUM_AT.
# ---------------------------------------------------------------------------


@proof
def GODELNUM_INJ(p):
    p.goal("!t1 t2. godelnum t1 = godelnum t2 ==> t1 = t2")
    p.fix("t1 t2")
    p.assume("h: godelnum t1 = godelnum t2")
    p.thus("t1 = t2").by_rewrite_of("h", [GODELNUM_AT])


# ---------------------------------------------------------------------------
# Size lemmas:  ``nat0_lt arg (Constructor ... arg ...)``.
#
# Each k-ary constructor wraps its arguments in ``Pair_ord tag arg``
# (k = 1) or ``Pair_ord tag (Pair_ord arg1 arg2)`` (k = 2). Combine
# NAT0_LT_PAIR_ORD_R (right-slot) and NAT0_LT_PAIR_ORD_L (left-slot)
# via NAT0_LT_TRANS to descend each layer; rewrite via the constructor
# ``_AT`` to fold the parent into constructor form.
# ---------------------------------------------------------------------------


# Helper: |- nat0_lt arg (Pair_ord tag arg) for a fixed tag.
# Caller passes a SPECL-instantiated NAT0_LT_PAIR_ORD_R as ``th``.
# (The proofs below just inline the SPECL.)


@proof
def NAT0_LT_SUCC_T(p):
    """|- !t. nat0_lt t (Succ_t t)."""
    from tactics import SYM, SPEC

    p.goal("!t. nat0_lt t (Succ_t t)")
    p.fix("t")
    succ_at_t = SPEC(p._parse("t"), SUCC_T_AT)
    # nat0_lt t (Pair_ord (SUC0 0) t).
    p.have("h: nat0_lt t (Pair_ord (SUC0 0) t)").by(
        NAT0_LT_PAIR_ORD_R, "SUC0 0", "t"
    )
    # Fold to Succ_t t.
    p.thus("nat0_lt t (Succ_t t)").by_rewrite_of(
        "h", [SYM(succ_at_t)]
    )


@proof
def NAT0_LT_VAR_T(p):
    """|- !v. nat0_lt v (Var_t v)."""
    from tactics import SYM, SPEC

    p.goal("!v. nat0_lt v (Var_t v)")
    p.fix("v")
    var_at_v = SPEC(p._parse("v"), VAR_T_AT)
    p.have("h: nat0_lt v (Pair_ord (SUC0 (SUC0 0)) v)").by(
        NAT0_LT_PAIR_ORD_R, "SUC0 (SUC0 0)", "v"
    )
    p.thus("nat0_lt v (Var_t v)").by_rewrite_of("h", [SYM(var_at_v)])


@proof
def NAT0_LT_NOT_F(p):
    """|- !phi. nat0_lt phi (Not_f phi)."""
    from tactics import SYM, SPEC

    p.goal("!phi. nat0_lt phi (Not_f phi)", types={"phi": "nat0"})
    p.fix("phi")
    not_at_phi = SPEC(p._parse("phi"), NOT_F_AT)
    p.have(
        "h: nat0_lt phi (Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))) phi)"
    ).by(
        NAT0_LT_PAIR_ORD_R, "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))", "phi"
    )
    p.thus("nat0_lt phi (Not_f phi)").by_rewrite_of(
        "h", [SYM(not_at_phi)]
    )


# ----- 2-arg (Insert-shape) size lemmas. -----
#
# For ``C a b = Pair_ord tag (Pair_ord a b)``:
#   nat0_lt a (Pair_ord a b)          (NAT0_LT_PAIR_ORD_L)
#   nat0_lt (Pair_ord a b) (Pair_ord tag (Pair_ord a b))    (NAT0_LT_PAIR_ORD_R)
#   chain via NAT0_LT_TRANS.


def _proof_lt_binary_left(thm_name, var_l, var_r, ctor_name, ctor_at, tag_str):
    """Build ``|- !{var_l} {var_r}. nat0_lt {var_l} ({ctor_name} {var_l} {var_r})``."""

    @proof
    def _THM(p):
        from tactics import SYM, SPECL

        p.goal(
            f"!{var_l} {var_r}. "
            f"nat0_lt {var_l} ({ctor_name} {var_l} {var_r})"
        )
        p.fix(f"{var_l} {var_r}")
        ctor_at_inst = SPECL(
            [p._parse(var_l), p._parse(var_r)], ctor_at
        )
        p.have(
            f"h1: nat0_lt {var_l} (Pair_ord {var_l} {var_r})"
        ).by(NAT0_LT_PAIR_ORD_L, var_l, var_r)
        p.have(
            f"h2: nat0_lt (Pair_ord {var_l} {var_r}) "
            f"(Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(
            NAT0_LT_PAIR_ORD_R,
            f"({tag_str})", f"Pair_ord {var_l} {var_r}",
        )
        p.have(
            f"h3: nat0_lt {var_l} "
            f"(Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(
            NAT0_LT_TRANS, var_l, f"Pair_ord {var_l} {var_r}",
            f"Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r})",
            "h1", "h2",
        )
        p.thus(
            f"nat0_lt {var_l} ({ctor_name} {var_l} {var_r})"
        ).by_rewrite_of("h3", [SYM(ctor_at_inst)])

    return _THM


def _proof_lt_binary_right(thm_name, var_l, var_r, ctor_name, ctor_at, tag_str):
    @proof
    def _THM(p):
        from tactics import SYM, SPECL

        p.goal(
            f"!{var_l} {var_r}. "
            f"nat0_lt {var_r} ({ctor_name} {var_l} {var_r})"
        )
        p.fix(f"{var_l} {var_r}")
        ctor_at_inst = SPECL(
            [p._parse(var_l), p._parse(var_r)], ctor_at
        )
        p.have(
            f"h1: nat0_lt {var_r} (Pair_ord {var_l} {var_r})"
        ).by(NAT0_LT_PAIR_ORD_R, var_l, var_r)
        p.have(
            f"h2: nat0_lt (Pair_ord {var_l} {var_r}) "
            f"(Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(
            NAT0_LT_PAIR_ORD_R,
            f"({tag_str})", f"Pair_ord {var_l} {var_r}",
        )
        p.have(
            f"h3: nat0_lt {var_r} "
            f"(Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(
            NAT0_LT_TRANS, var_r, f"Pair_ord {var_l} {var_r}",
            f"Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r})",
            "h1", "h2",
        )
        p.thus(
            f"nat0_lt {var_r} ({ctor_name} {var_l} {var_r})"
        ).by_rewrite_of("h3", [SYM(ctor_at_inst)])

    return _THM


# Tag literals for each binary constructor.
_PLUS_T_TAG = "SUC0 (SUC0 (SUC0 0))"
_TIMES_T_TAG = "SUC0 (SUC0 (SUC0 (SUC0 0)))"
_EQ_F_TAG = "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))"
_IMP_F_TAG = "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))))"
_FORALL_F_TAG = "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))))"


NAT0_LT_PLUS_T_L = _proof_lt_binary_left(
    "NAT0_LT_PLUS_T_L", "t1", "t2", "Plus_t", PLUS_T_AT, _PLUS_T_TAG
)
NAT0_LT_PLUS_T_R = _proof_lt_binary_right(
    "NAT0_LT_PLUS_T_R", "t1", "t2", "Plus_t", PLUS_T_AT, _PLUS_T_TAG
)
NAT0_LT_TIMES_T_L = _proof_lt_binary_left(
    "NAT0_LT_TIMES_T_L", "t1", "t2", "Times_t", TIMES_T_AT, _TIMES_T_TAG
)
NAT0_LT_TIMES_T_R = _proof_lt_binary_right(
    "NAT0_LT_TIMES_T_R", "t1", "t2", "Times_t", TIMES_T_AT, _TIMES_T_TAG
)
NAT0_LT_EQ_F_L = _proof_lt_binary_left(
    "NAT0_LT_EQ_F_L", "t1", "t2", "Eq_f", EQ_F_AT, _EQ_F_TAG
)
NAT0_LT_EQ_F_R = _proof_lt_binary_right(
    "NAT0_LT_EQ_F_R", "t1", "t2", "Eq_f", EQ_F_AT, _EQ_F_TAG
)
NAT0_LT_IMP_F_L = _proof_lt_binary_left(
    "NAT0_LT_IMP_F_L", "phi1", "phi2", "Imp_f", IMP_F_AT, _IMP_F_TAG
)
NAT0_LT_IMP_F_R = _proof_lt_binary_right(
    "NAT0_LT_IMP_F_R", "phi1", "phi2", "Imp_f", IMP_F_AT, _IMP_F_TAG
)
NAT0_LT_FORALL_F_L = _proof_lt_binary_left(
    "NAT0_LT_FORALL_F_L", "n", "phi", "Forall_f", FORALL_F_AT, _FORALL_F_TAG
)
NAT0_LT_FORALL_F_R = _proof_lt_binary_right(
    "NAT0_LT_FORALL_F_R", "n", "phi", "Forall_f", FORALL_F_AT, _FORALL_F_TAG
)


# ---------------------------------------------------------------------------
# Constructor injectivity.
#
# Unary:  C arg = Pair_ord tag arg, so C a = C b  =>  Pair_ord tag a =
#         Pair_ord tag b  =>  (tag = tag /\ a = b)  =>  a = b.
# Binary: C a b = Pair_ord tag (Pair_ord a b), so applying PAIR_ORD_INJ
#         twice yields a1 = a2 /\ b1 = b2.
# ---------------------------------------------------------------------------


@proof
def SUCC_T_INJ(p):
    """|- !a b. Succ_t a = Succ_t b ==> a = b."""
    from tactics import SYM, SPEC, CONJUNCT2

    p.goal("!a b. Succ_t a = Succ_t b ==> a = b")
    p.fix("a b")
    p.assume("h: Succ_t a = Succ_t b")
    succ_a = SPEC(p._parse("a"), SUCC_T_AT)
    succ_b = SPEC(p._parse("b"), SUCC_T_AT)
    p.have("h_po: Pair_ord (SUC0 0) a = Pair_ord (SUC0 0) b").by_rewrite_of(
        "h", [succ_a, succ_b]
    )
    p.have("h_inj: SUC0 0 = SUC0 0 /\\ a = b").by(
        PAIR_ORD_INJ, "SUC0 0", "a", "SUC0 0", "b", "h_po"
    )
    p.thus("a = b").by_thm(CONJUNCT2(p.fact("h_inj")))


@proof
def VAR_T_INJ(p):
    """|- !a b. Var_t a = Var_t b ==> a = b."""
    from tactics import SPEC, CONJUNCT2

    p.goal("!a b. Var_t a = Var_t b ==> a = b")
    p.fix("a b")
    p.assume("h: Var_t a = Var_t b")
    var_a = SPEC(p._parse("a"), VAR_T_AT)
    var_b = SPEC(p._parse("b"), VAR_T_AT)
    p.have(
        "h_po: Pair_ord (SUC0 (SUC0 0)) a = Pair_ord (SUC0 (SUC0 0)) b"
    ).by_rewrite_of("h", [var_a, var_b])
    p.have("h_inj: SUC0 (SUC0 0) = SUC0 (SUC0 0) /\\ a = b").by(
        PAIR_ORD_INJ, "SUC0 (SUC0 0)", "a", "SUC0 (SUC0 0)", "b", "h_po"
    )
    p.thus("a = b").by_thm(CONJUNCT2(p.fact("h_inj")))


@proof
def NOT_F_INJ(p):
    """|- !a b. Not_f a = Not_f b ==> a = b."""
    from tactics import SPEC, CONJUNCT2

    NOT_TAG = "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))"
    p.goal("!a b. Not_f a = Not_f b ==> a = b")
    p.fix("a b")
    p.assume("h: Not_f a = Not_f b")
    not_a = SPEC(p._parse("a"), NOT_F_AT)
    not_b = SPEC(p._parse("b"), NOT_F_AT)
    p.have(
        f"h_po: Pair_ord ({NOT_TAG}) a = Pair_ord ({NOT_TAG}) b"
    ).by_rewrite_of("h", [not_a, not_b])
    p.have(f"h_inj: {NOT_TAG} = {NOT_TAG} /\\ a = b").by(
        PAIR_ORD_INJ, f"({NOT_TAG})", "a", f"({NOT_TAG})", "b", "h_po"
    )
    p.thus("a = b").by_thm(CONJUNCT2(p.fact("h_inj")))


def _proof_binary_inj(thm_name, var_l1, var_r1, var_l2, var_r2,
                     ctor_name, ctor_at, tag_str):
    """Build ``|- !a1 b1 a2 b2. C a1 b1 = C a2 b2 ==> a1 = a2 /\\ b1 = b2``."""

    @proof
    def _THM(p):
        from tactics import SPECL, CONJUNCT2, CONJ

        p.goal(
            f"!{var_l1} {var_r1} {var_l2} {var_r2}. "
            f"{ctor_name} {var_l1} {var_r1} = {ctor_name} {var_l2} {var_r2} "
            f"==> ({var_l1} = {var_l2} /\\ {var_r1} = {var_r2})"
        )
        p.fix(f"{var_l1} {var_r1} {var_l2} {var_r2}")
        p.assume(
            f"h: {ctor_name} {var_l1} {var_r1} "
            f"= {ctor_name} {var_l2} {var_r2}"
        )
        c1 = SPECL([p._parse(var_l1), p._parse(var_r1)], ctor_at)
        c2 = SPECL([p._parse(var_l2), p._parse(var_r2)], ctor_at)
        # Outer Pair_ord_inj: tag-slot equality + (Pair_ord a1 b1 =
        # Pair_ord a2 b2).
        p.have(
            f"h_po: Pair_ord ({tag_str}) (Pair_ord {var_l1} {var_r1}) "
            f"= Pair_ord ({tag_str}) (Pair_ord {var_l2} {var_r2})"
        ).by_rewrite_of("h", [c1, c2])
        p.have(
            f"h_outer: ({tag_str}) = ({tag_str}) /\\ "
            f"Pair_ord {var_l1} {var_r1} = Pair_ord {var_l2} {var_r2}"
        ).by(
            PAIR_ORD_INJ,
            f"({tag_str})", f"Pair_ord {var_l1} {var_r1}",
            f"({tag_str})", f"Pair_ord {var_l2} {var_r2}",
            "h_po",
        )
        p.have(
            f"h_inner: Pair_ord {var_l1} {var_r1} "
            f"= Pair_ord {var_l2} {var_r2}"
        ).by_thm(CONJUNCT2(p.fact("h_outer")))
        p.have(
            f"h_split: {var_l1} = {var_l2} /\\ {var_r1} = {var_r2}"
        ).by(PAIR_ORD_INJ, var_l1, var_r1, var_l2, var_r2, "h_inner")
        p.thus(
            f"{var_l1} = {var_l2} /\\ {var_r1} = {var_r2}"
        ).by_thm(p.fact("h_split"))

    return _THM


PLUS_T_INJ = _proof_binary_inj(
    "PLUS_T_INJ", "a1", "a2", "b1", "b2", "Plus_t", PLUS_T_AT, _PLUS_T_TAG
)
TIMES_T_INJ = _proof_binary_inj(
    "TIMES_T_INJ", "a1", "a2", "b1", "b2", "Times_t", TIMES_T_AT, _TIMES_T_TAG
)
EQ_F_INJ = _proof_binary_inj(
    "EQ_F_INJ", "a1", "a2", "b1", "b2", "Eq_f", EQ_F_AT, _EQ_F_TAG
)
IMP_F_INJ = _proof_binary_inj(
    "IMP_F_INJ", "a1", "a2", "b1", "b2", "Imp_f", IMP_F_AT, _IMP_F_TAG
)
FORALL_F_INJ = _proof_binary_inj(
    "FORALL_F_INJ", "n1", "phi1", "n2", "phi2",
    "Forall_f", FORALL_F_AT, _FORALL_F_TAG,
)


# ---------------------------------------------------------------------------
# Constructor disjointness.
#
# Two cases:
#   (i)  Zero_t (= 0) vs any C(args). Each non-zero constructor is
#        ``Pair_ord tag (...)``, and ``In (Singleton tag) (Pair_ord
#        tag (...))`` holds (left disjunct of IN_PAIR_ORD); membership
#        forbids ``In _ 0`` (IN_ZERO), so the code is non-zero.
#   (ii) Two non-zero constructors with distinct tags. Apply
#        PAIR_ORD_INJ at slot 0 and contradict via tag-numeral
#        inequality.
#
# Tag-numeral inequalities are derived once per pair via the
# ``_neq_succ0`` helper below: AXIOM_3_0 plus iterated AXIOM_4_0
# unwraps SUC0-chains down to a 0-vs-(SUC0 _) base case.
# ---------------------------------------------------------------------------


def _suc0_chain(p, k):
    """Build the term string ``SUC0^k 0`` for a Python int ``k >= 0``."""
    s = "0"
    for _ in range(k):
        s = f"SUC0 ({s})"
    return s


@proof
def _NEQ_PAIR_ORD_ZERO(p):
    """|- !a b. ~(Pair_ord a b = 0).

    Directly: In (Singleton a) (Pair_ord a b) holds (left disjunct of
    IN_PAIR_ORD), but ~In (Singleton a) 0 (from IN_ZERO). The two
    contradict the assumed equation."""
    from fusion import REFL
    from tactics import SYM, EQT_ELIM, EQF_ELIM

    p.goal("!a b. ~(Pair_ord a b = 0)")
    p.fix("a b")
    with p.suppose("h: Pair_ord a b = 0"):
        # In (Singleton a) (Pair_ord a b) via left disjunct.
        p.have("hr: Singleton a = Singleton a").by_thm(
            REFL(p._parse("Singleton a"))
        )
        p.have(
            "hd: Singleton a = Singleton a \\/ Singleton a = Pair a b"
        ).by_disj("hr")
        p.have(
            "e1: In (Singleton a) (Pair_ord a b) = "
            "(Singleton a = Singleton a \\/ Singleton a = Pair a b)"
        ).by(IN_PAIR_ORD, "a", "b", "Singleton a")
        p.have("h_in: In (Singleton a) (Pair_ord a b)").by_eq_mp(
            SYM(p.fact("e1")), "hd"
        )
        # Transport to In (Singleton a) 0.
        p.have("h_in0: In (Singleton a) 0").by_rewrite_of("h_in", ["h"])
        p.have("e0: In (Singleton a) 0 = F").by(IN_ZERO, "Singleton a")
        p.have("h_neg: ~In (Singleton a) 0").by_thm(EQF_ELIM(p.fact("e0")))
        p.absurd().by_conj("h_neg", "h_in0")


# Tag inequality: SUC0^m 0 ≠ SUC0^n 0 when m ≠ n. We expose the small
# instances we need below; each follows from AXIOM_3_0 + iterated
# AXIOM_4_0 contrapositive.

def _prove_tag_neq(thm_name, m, n):
    """Build ``|- ~(SUC0^m 0 = SUC0^n 0)`` for ``m != n``.

    WLOG m < n. Strategy: assume the equation, peel m successors via
    AXIOM_4_0 to reduce to ``0 = SUC0^(n-m) 0``, contradict AXIOM_3_0.
    """
    if m == n:
        raise ValueError("_prove_tag_neq: m and n must differ")
    if m > n:
        return _prove_tag_neq(thm_name, n, m)  # by symmetry
    diff = n - m

    @proof
    def _THM(p):
        from tactics import SYM
        s_m = _suc0_chain(p, m)
        s_n = _suc0_chain(p, n)
        p.goal(f"~({s_m} = {s_n})")
        with p.suppose(f"h: {s_m} = {s_n}"):
            cur = "h"
            cur_m, cur_n = m, n
            for _ in range(m):
                # AXIOM_4_0 strips one SUC0 from each side.
                a = _suc0_chain(p, cur_m - 1)
                b = _suc0_chain(p, cur_n - 1)
                next_label = f"h_{cur_m - 1}_{cur_n - 1}"
                p.have(f"{next_label}: {a} = {b}").by(
                    AXIOM_4_0, a, b, cur
                )
                cur = next_label
                cur_m -= 1
                cur_n -= 1
            # cur : 0 = SUC0^diff 0.  ``diff >= 1`` so RHS = SUC0 (..).
            tail = _suc0_chain(p, diff - 1)
            # AXIOM_3_0 at tail: ~(SUC0 tail = 0). Symmetric to needed.
            p.have(f"h_neg: ~(SUC0 ({tail}) = 0)").by(AXIOM_3_0, tail)
            p.have(f"h_sym: SUC0 ({tail}) = 0").by_thm(SYM(p.fact(cur)))
            p.absurd().by_conj("h_neg", "h_sym")

    return _THM


# Tag inequalities for pairs (m, n) with m < n in {0..8}. We build all
# 36 once; each is ~5-10 lines through _prove_tag_neq's loop.

_TAG_NEQS = {}
for _m in range(9):
    for _n in range(_m + 1, 9):
        _TAG_NEQS[(_m, _n)] = _prove_tag_neq(f"_TAG_NEQ_{_m}_{_n}", _m, _n)


# ---------------------------------------------------------------------------
# "Constructor C ≠ 0" disjointness lemmas.  Each non-zero constructor's
# code is a Pair_ord, and Pair_ord _ _ ≠ 0 by _NEQ_PAIR_ORD_ZERO.
# ---------------------------------------------------------------------------


def _proof_ctor_neq_zero_unary(thm_name, var, ctor_name, ctor_at, tag_str):
    @proof
    def _THM(p):
        from tactics import SPEC

        p.goal(f"!{var}. ~({ctor_name} {var} = Zero_t)")
        p.fix(var)
        ctor_inst = SPEC(p._parse(var), ctor_at)
        with p.suppose(f"h: {ctor_name} {var} = Zero_t"):
            p.have(f"h_po: Pair_ord ({tag_str}) {var} = 0").by_rewrite_of(
                "h", [ctor_inst, ZERO_T_DEF]
            )
            p.have(f"h_neg: ~(Pair_ord ({tag_str}) {var} = 0)").by(
                _NEQ_PAIR_ORD_ZERO, f"({tag_str})", var
            )
            p.absurd().by_conj("h_neg", "h_po")

    return _THM


def _proof_ctor_neq_zero_binary(thm_name, var_l, var_r, ctor_name, ctor_at, tag_str):
    @proof
    def _THM(p):
        from tactics import SPECL

        p.goal(
            f"!{var_l} {var_r}. ~({ctor_name} {var_l} {var_r} = Zero_t)"
        )
        p.fix(f"{var_l} {var_r}")
        ctor_inst = SPECL([p._parse(var_l), p._parse(var_r)], ctor_at)
        with p.suppose(f"h: {ctor_name} {var_l} {var_r} = Zero_t"):
            p.have(
                f"h_po: Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}) = 0"
            ).by_rewrite_of("h", [ctor_inst, ZERO_T_DEF])
            p.have(
                f"h_neg: ~(Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}) = 0)"
            ).by(
                _NEQ_PAIR_ORD_ZERO,
                f"({tag_str})", f"Pair_ord {var_l} {var_r}",
            )
            p.absurd().by_conj("h_neg", "h_po")

    return _THM


_SUCC_T_TAG = "SUC0 0"
_VAR_T_TAG = "SUC0 (SUC0 0)"
_NOT_F_TAG = "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))"


SUCC_T_NEQ_ZERO = _proof_ctor_neq_zero_unary(
    "SUCC_T_NEQ_ZERO", "t", "Succ_t", SUCC_T_AT, _SUCC_T_TAG
)
VAR_T_NEQ_ZERO = _proof_ctor_neq_zero_unary(
    "VAR_T_NEQ_ZERO", "v", "Var_t", VAR_T_AT, _VAR_T_TAG
)
NOT_F_NEQ_ZERO = _proof_ctor_neq_zero_unary(
    "NOT_F_NEQ_ZERO", "phi", "Not_f", NOT_F_AT, _NOT_F_TAG
)
PLUS_T_NEQ_ZERO = _proof_ctor_neq_zero_binary(
    "PLUS_T_NEQ_ZERO", "t1", "t2", "Plus_t", PLUS_T_AT, _PLUS_T_TAG
)
TIMES_T_NEQ_ZERO = _proof_ctor_neq_zero_binary(
    "TIMES_T_NEQ_ZERO", "t1", "t2", "Times_t", TIMES_T_AT, _TIMES_T_TAG
)
EQ_F_NEQ_ZERO = _proof_ctor_neq_zero_binary(
    "EQ_F_NEQ_ZERO", "t1", "t2", "Eq_f", EQ_F_AT, _EQ_F_TAG
)
IMP_F_NEQ_ZERO = _proof_ctor_neq_zero_binary(
    "IMP_F_NEQ_ZERO", "phi1", "phi2", "Imp_f", IMP_F_AT, _IMP_F_TAG
)
FORALL_F_NEQ_ZERO = _proof_ctor_neq_zero_binary(
    "FORALL_F_NEQ_ZERO", "n", "phi", "Forall_f", FORALL_F_AT, _FORALL_F_TAG
)


# ---------------------------------------------------------------------------
# "Distinct non-zero constructors are unequal" disjointness.
#
# Each pair ``C1 args1 = C2 args2`` rewrites to a Pair_ord-at-slot-0
# tag-equality plus an inner Pair_ord-equality. The tag-equality
# contradicts the corresponding tag-inequality from ``_TAG_NEQS``.
# ---------------------------------------------------------------------------


def _ctor_decl(ctor_name, ctor_at, tag_idx, vars_, tag_str):
    """Bundle for a constructor: name string, AT theorem, tag index
    (0..8), variable names list, tag SUC0-chain string."""
    return (ctor_name, ctor_at, tag_idx, vars_, tag_str)


_CTORS = {
    "Succ_t": _ctor_decl("Succ_t", SUCC_T_AT, 1, ["t"], _SUCC_T_TAG),
    "Var_t":  _ctor_decl("Var_t", VAR_T_AT, 2, ["v"], _VAR_T_TAG),
    "Plus_t": _ctor_decl("Plus_t", PLUS_T_AT, 3, ["t1", "t2"], _PLUS_T_TAG),
    "Times_t": _ctor_decl("Times_t", TIMES_T_AT, 4, ["t1", "t2"], _TIMES_T_TAG),
    "Eq_f":   _ctor_decl("Eq_f", EQ_F_AT, 5, ["t1", "t2"], _EQ_F_TAG),
    "Not_f":  _ctor_decl("Not_f", NOT_F_AT, 6, ["phi"], _NOT_F_TAG),
    "Imp_f":  _ctor_decl("Imp_f", IMP_F_AT, 7, ["phi1", "phi2"], _IMP_F_TAG),
    "Forall_f": _ctor_decl(
        "Forall_f", FORALL_F_AT, 8, ["n", "phi"], _FORALL_F_TAG
    ),
}


def _ctor_inner_arg(ctor_decl, suffix):
    """For a unary constructor returns ``v{suffix}``; for binary
    returns ``Pair_ord v_l{suffix} v_r{suffix}``."""
    name, _at, _idx, vars_, _tag = ctor_decl
    if len(vars_) == 1:
        return f"{vars_[0]}{suffix}"
    a, b = vars_
    return f"Pair_ord {a}{suffix} {b}{suffix}"


def _proof_ctor_disjoint(thm_name, ctor1_name, ctor2_name):
    decl1 = _CTORS[ctor1_name]
    decl2 = _CTORS[ctor2_name]
    name1, at1, tag1_idx, vars1, tag1 = decl1
    name2, at2, tag2_idx, vars2, tag2 = decl2
    if tag1_idx == tag2_idx:
        raise ValueError(f"identical tags for {ctor1_name} vs {ctor2_name}")
    # Build fresh variable suffixes "1" / "2" to avoid name collision
    # when the two constructors share variable letters.
    fix_vars1 = [f"{v}1" for v in vars1]
    fix_vars2 = [f"{v}2" for v in vars2]
    all_vars = fix_vars1 + fix_vars2
    args1 = " ".join(fix_vars1)
    args2 = " ".join(fix_vars2)

    @proof
    def _THM(p):
        from tactics import SPECL, CONJUNCT1

        p.goal(
            f"!{' '.join(all_vars)}. "
            f"~({name1} {args1} = {name2} {args2})"
        )
        p.fix(" ".join(all_vars))
        c1 = SPECL([p._parse(v) for v in fix_vars1], at1)
        c2 = SPECL([p._parse(v) for v in fix_vars2], at2)
        with p.suppose(f"h: {name1} {args1} = {name2} {args2}"):
            inner1 = _ctor_inner_arg(decl1, "1")
            inner2 = _ctor_inner_arg(decl2, "2")
            p.have(
                f"h_po: Pair_ord ({tag1}) ({inner1}) "
                f"= Pair_ord ({tag2}) ({inner2})"
            ).by_rewrite_of("h", [c1, c2])
            p.have(
                f"h_inj: ({tag1}) = ({tag2}) /\\ ({inner1}) = ({inner2})"
            ).by(
                PAIR_ORD_INJ,
                f"({tag1})", f"({inner1})",
                f"({tag2})", f"({inner2})",
                "h_po",
            )
            p.have(f"h_tag: ({tag1}) = ({tag2})").by_thm(
                CONJUNCT1(p.fact("h_inj"))
            )
            # Tag inequality.
            lo, hi = sorted([tag1_idx, tag2_idx])
            tag_neq = _TAG_NEQS[(lo, hi)]
            if tag1_idx < tag2_idx:
                p.have(
                    f"h_tag_neq: ~(({tag1}) = ({tag2}))"
                ).by_thm(tag_neq)
                p.absurd().by_conj("h_tag_neq", "h_tag")
            else:
                # _TAG_NEQS is keyed (lo, hi) so the lemma's conclusion
                # is ~(SUC0^lo 0 = SUC0^hi 0); flip to match h_tag.
                from tactics import SYM
                p.have(
                    f"h_tag_sym: ({tag2}) = ({tag1})"
                ).by_thm(SYM(p.fact("h_tag")))
                p.have(
                    f"h_tag_neq: ~(({tag2}) = ({tag1}))"
                ).by_thm(tag_neq)
                p.absurd().by_conj("h_tag_neq", "h_tag_sym")

    return _THM


# Pairwise disjointness for the 8 non-zero constructors. We expose
# ``CTOR1_NEQ_CTOR2`` for each ordered pair (lexicographic by tag).

_CTOR_NAMES = ["Succ_t", "Var_t", "Plus_t", "Times_t",
               "Eq_f", "Not_f", "Imp_f", "Forall_f"]

CTOR_DISJOINTNESS = {}  # (name1, name2) -> theorem
for _i in range(len(_CTOR_NAMES)):
    for _j in range(_i + 1, len(_CTOR_NAMES)):
        _n1, _n2 = _CTOR_NAMES[_i], _CTOR_NAMES[_j]
        CTOR_DISJOINTNESS[(_n1, _n2)] = _proof_ctor_disjoint(
            f"{_n1.upper()}_NEQ_{_n2.upper()}", _n1, _n2,
        )


# ---------------------------------------------------------------------------
# Stage 1 (b)/(c) work to follow:
#   * is_term, is_form, substitute, free_in via define_wf_lt with
#     NUM_RECURSION_LT-based MONO proofs. Each ~30 (body) + ~80-120
#     (MONO) + ~20 (define_wf_lt + REC) lines, plus ~5 lines per
#     constructor-specific recursion equation.  Total ~600 lines.
# ---------------------------------------------------------------------------


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 1 (a) -- term/form datatype + godelnum injectivity.")
    print("  Term constructors:")
    print("    ZERO_T_DEF    :", pp_thm(ZERO_T_DEF))
    print("    SUCC_T_DEF    :", pp_thm(SUCC_T_DEF))
    print("    SUCC_T_AT     :", pp_thm(SUCC_T_AT))
    print("    VAR_T_DEF     :", pp_thm(VAR_T_DEF))
    print("    VAR_T_AT      :", pp_thm(VAR_T_AT))
    print("    PLUS_T_DEF    :", pp_thm(PLUS_T_DEF))
    print("    PLUS_T_AT     :", pp_thm(PLUS_T_AT))
    print("    TIMES_T_DEF   :", pp_thm(TIMES_T_DEF))
    print("    TIMES_T_AT    :", pp_thm(TIMES_T_AT))
    print("  Form constructors:")
    print("    EQ_F_DEF      :", pp_thm(EQ_F_DEF))
    print("    EQ_F_AT       :", pp_thm(EQ_F_AT))
    print("    NOT_F_DEF     :", pp_thm(NOT_F_DEF))
    print("    NOT_F_AT      :", pp_thm(NOT_F_AT))
    print("    IMP_F_DEF     :", pp_thm(IMP_F_DEF))
    print("    IMP_F_AT      :", pp_thm(IMP_F_AT))
    print("    FORALL_F_DEF  :", pp_thm(FORALL_F_DEF))
    print("    FORALL_F_AT   :", pp_thm(FORALL_F_AT))
    print("  Goedel numbering:")
    print("    GODELNUM_DEF  :", pp_thm(GODELNUM_DEF))
    print("    GODELNUM_AT   :", pp_thm(GODELNUM_AT))
    print("    GODELNUM_INJ  :", pp_thm(GODELNUM_INJ))
    print()
    print("Stage 1 -- size lemmas (foundation for define_wf_lt MONO proofs).")
    print("  Unary constructors:")
    print("    NAT0_LT_SUCC_T  :", pp_thm(NAT0_LT_SUCC_T))
    print("    NAT0_LT_VAR_T   :", pp_thm(NAT0_LT_VAR_T))
    print("    NAT0_LT_NOT_F   :", pp_thm(NAT0_LT_NOT_F))
    print("  Binary constructors (left / right slot):")
    print("    NAT0_LT_PLUS_T_L  :", pp_thm(NAT0_LT_PLUS_T_L))
    print("    NAT0_LT_PLUS_T_R  :", pp_thm(NAT0_LT_PLUS_T_R))
    print("    NAT0_LT_TIMES_T_L :", pp_thm(NAT0_LT_TIMES_T_L))
    print("    NAT0_LT_TIMES_T_R :", pp_thm(NAT0_LT_TIMES_T_R))
    print("    NAT0_LT_EQ_F_L    :", pp_thm(NAT0_LT_EQ_F_L))
    print("    NAT0_LT_EQ_F_R    :", pp_thm(NAT0_LT_EQ_F_R))
    print("    NAT0_LT_IMP_F_L   :", pp_thm(NAT0_LT_IMP_F_L))
    print("    NAT0_LT_IMP_F_R   :", pp_thm(NAT0_LT_IMP_F_R))
    print("    NAT0_LT_FORALL_F_L:", pp_thm(NAT0_LT_FORALL_F_L))
    print("    NAT0_LT_FORALL_F_R:", pp_thm(NAT0_LT_FORALL_F_R))
    print()
    print("Stage 1 -- constructor injectivity.")
    print("  Unary:")
    print("    SUCC_T_INJ    :", pp_thm(SUCC_T_INJ))
    print("    VAR_T_INJ     :", pp_thm(VAR_T_INJ))
    print("    NOT_F_INJ     :", pp_thm(NOT_F_INJ))
    print("  Binary:")
    print("    PLUS_T_INJ    :", pp_thm(PLUS_T_INJ))
    print("    TIMES_T_INJ   :", pp_thm(TIMES_T_INJ))
    print("    EQ_F_INJ      :", pp_thm(EQ_F_INJ))
    print("    IMP_F_INJ     :", pp_thm(IMP_F_INJ))
    print("    FORALL_F_INJ  :", pp_thm(FORALL_F_INJ))
    print()
    print("Stage 1 -- constructor disjointness.")
    print("  Each non-zero constructor C: !args. ~(C args = Zero_t):")
    print("    SUCC_T_NEQ_ZERO   :", pp_thm(SUCC_T_NEQ_ZERO))
    print("    VAR_T_NEQ_ZERO    :", pp_thm(VAR_T_NEQ_ZERO))
    print("    NOT_F_NEQ_ZERO    :", pp_thm(NOT_F_NEQ_ZERO))
    print("    PLUS_T_NEQ_ZERO   :", pp_thm(PLUS_T_NEQ_ZERO))
    print("    TIMES_T_NEQ_ZERO  :", pp_thm(TIMES_T_NEQ_ZERO))
    print("    EQ_F_NEQ_ZERO     :", pp_thm(EQ_F_NEQ_ZERO))
    print("    IMP_F_NEQ_ZERO    :", pp_thm(IMP_F_NEQ_ZERO))
    print("    FORALL_F_NEQ_ZERO :", pp_thm(FORALL_F_NEQ_ZERO))
    print(f"  Pairwise distinct-tag disjointness: "
          f"{len(CTOR_DISJOINTNESS)} lemmas, e.g.")
    print("    SUCC_T_NEQ_VAR_T  :",
          pp_thm(CTOR_DISJOINTNESS[('Succ_t', 'Var_t')]))
    print("    PLUS_T_NEQ_TIMES_T:",
          pp_thm(CTOR_DISJOINTNESS[('Plus_t', 'Times_t')]))
    print("    EQ_F_NEQ_FORALL_F :",
          pp_thm(CTOR_DISJOINTNESS[('Eq_f', 'Forall_f')]))
    print()
    print("Stage 1 (b)+(c) -- is_term, is_form, substitute, free_in: TODO.")
