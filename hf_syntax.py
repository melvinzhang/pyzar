# ---------------------------------------------------------------------------
# Stage 1 -- syntax of HF (Świerczkowski's grammar) encoded as nat0.
# ---------------------------------------------------------------------------
#
# Świerczkowski's signature for HF: empty set, set-insertion, membership,
# equality, plus first-order connectives and quantifiers:
#
#   Term  ::=  Empty | Var num | Insert Term Term
#   Form  ::=  Eq Term Term | In Term Term
#           |  Not Form | Imp Form Form | Forall num Form
#
# (And, Or, Exists, Iff are sugar.) Each constructor has an arity; encode
# a node ``Constructor(arg1, ..., argk)`` as nested ``Pair_ord`` layers
# with a unique tag at slot 0.

r"""Syntax of HF encoded as nat0 (Stage 1 of ``godel_first.py``).

------------------------------------------------------------------
Encoding (flat pairing)
------------------------------------------------------------------

Term/Form grammar (Świerczkowski 2003):

    Term  ::=  Empty | Var num | Insert Term Term
    Form  ::=  Eq Term Term | In Term Term
            |  Not Form | Imp Form Form | Forall num Form

The encoding flattens each constructor onto ``Pair_ord`` from
``hf_sets.py`` (the Kuratowski ordered pair, which is itself a nat0):

    Empty_t           :=  0
    Var_t  v          :=  Pair_ord 2 v
    Eq_f    t1 t2     :=  Pair_ord 5 (Pair_ord t1 t2)
    Not_f   F         :=  Pair_ord 6 F
    Imp_f   F1 F2     :=  Pair_ord 7 (Pair_ord F1 F2)
    Forall_f n F      :=  Pair_ord 8 (Pair_ord n F)
    Insert_t t1 t2    :=  Pair_ord 9 (Pair_ord t1 t2)
    In_a   t1 t2      :=  Pair_ord 10 (Pair_ord t1 t2)

Tags are distinct nat0 numerals; arity-2 constructors curry their
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

Constructor injectivity (e.g. ``Insert_t a b = Insert_t c d ==> a=c /\ b=d``)
unfolds to one or two applications of PAIR_ORD_INJ; size lemmas
(e.g. ``nat0_lt t1 (Insert_t t1 t2)``) are one or two applications of the
NAT0_LT_PAIR_ORD pair, chained via ``NAT0_LT_TRANS``. Disjointness
between distinct constructors follows from PAIR_ORD_INJ at slot 0
and tag-numeral inequalities (``~(SUC0 (SUC0 0) = SUC0 0)`` etc.).

With ``hf_ty = nat0_ty`` (no nominal subtype), every constructor
output is already a bona fide ``nat0`` -- the encoded HF tree IS its
own Goedel number, so no separate godelnum-of-tree wrapper is needed.
"""

# ---------------------------------------------------------------------------
# Imports.
# ---------------------------------------------------------------------------

from fusion import Var, ASSUME, DEDUCT_ANTISYM_RULE, REFL, vsubst, INST_TYPE
from basics import mk_const, mk_app, mk_eq, mk_abs, dest_eq, is_eq, rator, rand
from parser import define, parse_type
from axioms import (
    F,
    mk_and,
    mk_exists,
    mk_not,
    mk_or,
    mk_select,
    dest_conj,
    dest_forall,
    dest_imp,
    dest_exists,
    dest_disj,
    SELECT_AX,
    aty,
)
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
from nat0_order import NAT0_LT_TRANS, define_wf_lt
from proof import proof, define_with_at
from fusion import ABS
from classical import EXCLUDED_MIDDLE
from tactics import (
    SPEC,
    SPECL,
    GEN,
    GENL,
    SYM,
    EQ_MP,
    MP,
    CONJ,
    CONJUNCT1,
    CONJUNCT2,
    EXISTS,
    CHOOSE_WITNESS,
    REWRITE_RULE,
    REWRITE_CONV,
    EQF_INTRO,
    NOT_ELIM,
    DISCH,
    CONTR,
    TRANS,
    AP_TERM,
    AP_THM,
    BETA_CONV,
    BETA_NORM,
    DISJ1,
    DISJ2,
    DISJ_CASES,
    or_chain_collapse,
)


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
# with a unique tag at slot 0. Tags are nat0 numerals written as SUC0
# chains so they normalise to closed numerical values.
# ---------------------------------------------------------------------------

VAR_T_DEF, VAR_T_AT = define_with_at(
    "Var_t",
    parse_type("nat0 -> nat0"),
    "\\v:nat0. Pair_ord (SUC0 (SUC0 0)) v",
)
Var_t = mk_const("Var_t", [])


# ---------------------------------------------------------------------------
# Form constructors.
# ---------------------------------------------------------------------------

EQ_F_DEF, EQ_F_AT = define_with_at(
    "Eq_f",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\t1:nat0. \\t2:nat0. "
    "Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))) (Pair_ord t1 t2)",
)
Eq_f = mk_const("Eq_f", [])

NOT_F_DEF, NOT_F_AT = define_with_at(
    "Not_f",
    parse_type("nat0 -> nat0"),
    "\\phi:nat0. Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))) phi",
)
Not_f = mk_const("Not_f", [])

IMP_F_DEF, IMP_F_AT = define_with_at(
    "Imp_f",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\phi1:nat0. \\phi2:nat0. "
    "Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))))) "
    "(Pair_ord phi1 phi2)",
)
Imp_f = mk_const("Imp_f", [])

FORALL_F_DEF, FORALL_F_AT = define_with_at(
    "Forall_f",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\n:nat0. \\phi:nat0. "
    "Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))))) "
    "(Pair_ord n phi)",
)
Forall_f = mk_const("Forall_f", [])


# ---------------------------------------------------------------------------
# HF primitives -- Empty_t (nullary base, encoded as 0), Insert_t (set
# adjunction), In_a (membership). The structural recognisers below
# (is_term, is_form, free_in, substitute) all carry matching disjuncts
# and AT-equations for these constructors:
#   * is_term recognises Empty_t (atomic) and Insert_t (binary recursive).
#   * is_form recognises In_a (atomic; both slots checked via is_term).
#   * free_in / substitute have AT-equations for all of them.
# ---------------------------------------------------------------------------

EMPTY_T_DEF = define("Empty_t", parse_type("nat0"), "0")
Empty_t = mk_const("Empty_t", [])

INSERT_T_DEF, INSERT_T_AT = define_with_at(
    "Insert_t",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\t1:nat0. \\t2:nat0. "
    "Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))))))) "
    "(Pair_ord t1 t2)",
)
Insert_t = mk_const("Insert_t", [])

IN_A_DEF, IN_A_AT = define_with_at(
    "In_a",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\t1:nat0. \\t2:nat0. "
    "Pair_ord "
    "(SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))))))) "
    "(Pair_ord t1 t2)",
)
In_a = mk_const("In_a", [])


# Pointwise applied forms (``VAR_T_AT`` etc.) are produced alongside the
# defining equations above via ``define_with_at``.  Downstream rewrites
# pattern-match on the applied head.


# Note on Gödel-numbering: with ``hf_ty = nat0_ty`` (no nominal
# subtype) and the Pair_ord-based encoding above, every constructor
# output is already a bona fide nat0 -- the encoded HF tree IS its
# own Gödel number, so no separate ``godelnum`` function is needed.


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
    ).by(NAT0_LT_PAIR_ORD_R, "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))", "phi")
    p.thus("nat0_lt phi (Not_f phi)").by_rewrite_of("h", [SYM(not_at_phi)])


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

        p.goal(f"!{var_l} {var_r}. nat0_lt {var_l} ({ctor_name} {var_l} {var_r})")
        p.fix(f"{var_l} {var_r}")
        ctor_at_inst = SPECL([p._parse(var_l), p._parse(var_r)], ctor_at)
        p.have(f"h1: nat0_lt {var_l} (Pair_ord {var_l} {var_r})").by(
            NAT0_LT_PAIR_ORD_L, var_l, var_r
        )
        p.have(
            f"h2: nat0_lt (Pair_ord {var_l} {var_r}) "
            f"(Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(
            NAT0_LT_PAIR_ORD_R,
            f"({tag_str})",
            f"Pair_ord {var_l} {var_r}",
        )
        p.have(
            f"h3: nat0_lt {var_l} (Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(
            NAT0_LT_TRANS,
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


def _proof_lt_binary_right(thm_name, var_l, var_r, ctor_name, ctor_at, tag_str):
    @proof
    def _THM(p):
        from tactics import SYM, SPECL

        p.goal(f"!{var_l} {var_r}. nat0_lt {var_r} ({ctor_name} {var_l} {var_r})")
        p.fix(f"{var_l} {var_r}")
        ctor_at_inst = SPECL([p._parse(var_l), p._parse(var_r)], ctor_at)
        p.have(f"h1: nat0_lt {var_r} (Pair_ord {var_l} {var_r})").by(
            NAT0_LT_PAIR_ORD_R, var_l, var_r
        )
        p.have(
            f"h2: nat0_lt (Pair_ord {var_l} {var_r}) "
            f"(Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(
            NAT0_LT_PAIR_ORD_R,
            f"({tag_str})",
            f"Pair_ord {var_l} {var_r}",
        )
        p.have(
            f"h3: nat0_lt {var_r} (Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}))"
        ).by(
            NAT0_LT_TRANS,
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


# Tag literals for each binary constructor.
_EQ_F_TAG = "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))"
_IMP_F_TAG = "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))))"
_FORALL_F_TAG = "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))))"


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

# HF size lemmas (tags 9, 10).
_INSERT_T_TAG = "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))))))"
_IN_A_TAG = "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))))))"
NAT0_LT_INSERT_T_L = _proof_lt_binary_left(
    "NAT0_LT_INSERT_T_L", "t1", "t2", "Insert_t", INSERT_T_AT, _INSERT_T_TAG
)
NAT0_LT_INSERT_T_R = _proof_lt_binary_right(
    "NAT0_LT_INSERT_T_R", "t1", "t2", "Insert_t", INSERT_T_AT, _INSERT_T_TAG
)
NAT0_LT_IN_A_L = _proof_lt_binary_left(
    "NAT0_LT_IN_A_L", "t1", "t2", "In_a", IN_A_AT, _IN_A_TAG
)
NAT0_LT_IN_A_R = _proof_lt_binary_right(
    "NAT0_LT_IN_A_R", "t1", "t2", "In_a", IN_A_AT, _IN_A_TAG
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
    p.have(f"h_po: Pair_ord ({NOT_TAG}) a = Pair_ord ({NOT_TAG}) b").by_rewrite_of(
        "h", [not_a, not_b]
    )
    p.have(f"h_inj: {NOT_TAG} = {NOT_TAG} /\\ a = b").by(
        PAIR_ORD_INJ, f"({NOT_TAG})", "a", f"({NOT_TAG})", "b", "h_po"
    )
    p.thus("a = b").by_thm(CONJUNCT2(p.fact("h_inj")))


def _proof_binary_inj(
    thm_name, var_l1, var_r1, var_l2, var_r2, ctor_name, ctor_at, tag_str
):
    """Build ``|- !a1 b1 a2 b2. C a1 b1 = C a2 b2 ==> a1 = a2 /\\ b1 = b2``."""

    @proof
    def _THM(p):
        from tactics import SPECL, CONJUNCT2

        p.goal(
            f"!{var_l1} {var_r1} {var_l2} {var_r2}. "
            f"{ctor_name} {var_l1} {var_r1} = {ctor_name} {var_l2} {var_r2} "
            f"==> ({var_l1} = {var_l2} /\\ {var_r1} = {var_r2})"
        )
        p.fix(f"{var_l1} {var_r1} {var_l2} {var_r2}")
        p.assume(f"h: {ctor_name} {var_l1} {var_r1} = {ctor_name} {var_l2} {var_r2}")
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
            f"({tag_str})",
            f"Pair_ord {var_l1} {var_r1}",
            f"({tag_str})",
            f"Pair_ord {var_l2} {var_r2}",
            "h_po",
        )
        p.have(
            f"h_inner: Pair_ord {var_l1} {var_r1} = Pair_ord {var_l2} {var_r2}"
        ).by_thm(CONJUNCT2(p.fact("h_outer")))
        p.have(f"h_split: {var_l1} = {var_l2} /\\ {var_r1} = {var_r2}").by(
            PAIR_ORD_INJ, var_l1, var_r1, var_l2, var_r2, "h_inner"
        )
        p.thus(f"{var_l1} = {var_l2} /\\ {var_r1} = {var_r2}").by_thm(p.fact("h_split"))

    return _THM


EQ_F_INJ = _proof_binary_inj(
    "EQ_F_INJ", "a1", "a2", "b1", "b2", "Eq_f", EQ_F_AT, _EQ_F_TAG
)
IMP_F_INJ = _proof_binary_inj(
    "IMP_F_INJ", "a1", "a2", "b1", "b2", "Imp_f", IMP_F_AT, _IMP_F_TAG
)
FORALL_F_INJ = _proof_binary_inj(
    "FORALL_F_INJ",
    "n1",
    "phi1",
    "n2",
    "phi2",
    "Forall_f",
    FORALL_F_AT,
    _FORALL_F_TAG,
)
INSERT_T_INJ = _proof_binary_inj(
    "INSERT_T_INJ", "a1", "b1", "a2", "b2", "Insert_t", INSERT_T_AT, _INSERT_T_TAG
)
IN_A_INJ = _proof_binary_inj(
    "IN_A_INJ", "a1", "b1", "a2", "b2", "In_a", IN_A_AT, _IN_A_TAG
)


# ---------------------------------------------------------------------------
# Constructor disjointness.
#
# Two cases:
#   (i)  Empty_t (= 0) vs any C(args). Each non-empty constructor is
#        ``Pair_ord tag (...)``, and ``In (Singleton tag) (Pair_ord
#        tag (...))`` holds (left disjunct of IN_PAIR_ORD); membership
#        forbids ``In _ 0`` (IN_ZERO), so the code is non-zero.
#   (ii) Two non-empty constructors with distinct tags. Apply
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
    from tactics import SYM, EQF_ELIM

    p.goal("!a b. ~(Pair_ord a b = 0)")
    p.fix("a b")
    with p.suppose("h: Pair_ord a b = 0"):
        # In (Singleton a) (Pair_ord a b) via left disjunct.
        p.have("hr: Singleton a = Singleton a").by_thm(REFL(p._parse("Singleton a")))
        p.have("hd: Singleton a = Singleton a \\/ Singleton a = Pair a b").by_disj("hr")
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
                p.have(f"{next_label}: {a} = {b}").by(AXIOM_4_0, a, b, cur)
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


# Tag inequalities for pairs (m, n) with m < n in {0..10}. We build them
# all once; each is ~5-10 lines through _prove_tag_neq's loop.

_TAG_NEQS = {}
for _m in range(11):
    for _n in range(_m + 1, 11):
        _TAG_NEQS[(_m, _n)] = _prove_tag_neq(f"_TAG_NEQ_{_m}_{_n}", _m, _n)


# ---------------------------------------------------------------------------
# "Constructor C ≠ Empty_t" disjointness lemmas. Each non-empty
# constructor's code is a Pair_ord, and Pair_ord _ _ ≠ 0 by
# _NEQ_PAIR_ORD_ZERO.
# ---------------------------------------------------------------------------


def _proof_ctor_neq_empty_unary(thm_name, var, ctor_name, ctor_at, tag_str):
    @proof
    def _THM(p):
        from tactics import SPEC

        p.goal(f"!{var}. ~({ctor_name} {var} = Empty_t)")
        p.fix(var)
        ctor_inst = SPEC(p._parse(var), ctor_at)
        with p.suppose(f"h: {ctor_name} {var} = Empty_t"):
            p.have(f"h_po: Pair_ord ({tag_str}) {var} = 0").by_rewrite_of(
                "h", [ctor_inst, EMPTY_T_DEF]
            )
            p.have(f"h_neg: ~(Pair_ord ({tag_str}) {var} = 0)").by(
                _NEQ_PAIR_ORD_ZERO, f"({tag_str})", var
            )
            p.absurd().by_conj("h_neg", "h_po")

    return _THM


def _proof_ctor_neq_empty_binary(thm_name, var_l, var_r, ctor_name, ctor_at, tag_str):
    @proof
    def _THM(p):
        from tactics import SPECL

        p.goal(f"!{var_l} {var_r}. ~({ctor_name} {var_l} {var_r} = Empty_t)")
        p.fix(f"{var_l} {var_r}")
        ctor_inst = SPECL([p._parse(var_l), p._parse(var_r)], ctor_at)
        with p.suppose(f"h: {ctor_name} {var_l} {var_r} = Empty_t"):
            p.have(
                f"h_po: Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}) = 0"
            ).by_rewrite_of("h", [ctor_inst, EMPTY_T_DEF])
            p.have(f"h_neg: ~(Pair_ord ({tag_str}) (Pair_ord {var_l} {var_r}) = 0)").by(
                _NEQ_PAIR_ORD_ZERO,
                f"({tag_str})",
                f"Pair_ord {var_l} {var_r}",
            )
            p.absurd().by_conj("h_neg", "h_po")

    return _THM


_VAR_T_TAG = "SUC0 (SUC0 0)"
_NOT_F_TAG = "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))"


VAR_T_NEQ_EMPTY = _proof_ctor_neq_empty_unary(
    "VAR_T_NEQ_EMPTY", "v", "Var_t", VAR_T_AT, _VAR_T_TAG
)
NOT_F_NEQ_EMPTY = _proof_ctor_neq_empty_unary(
    "NOT_F_NEQ_EMPTY", "phi", "Not_f", NOT_F_AT, _NOT_F_TAG
)
EQ_F_NEQ_EMPTY = _proof_ctor_neq_empty_binary(
    "EQ_F_NEQ_EMPTY", "t1", "t2", "Eq_f", EQ_F_AT, _EQ_F_TAG
)
IMP_F_NEQ_EMPTY = _proof_ctor_neq_empty_binary(
    "IMP_F_NEQ_EMPTY", "phi1", "phi2", "Imp_f", IMP_F_AT, _IMP_F_TAG
)
FORALL_F_NEQ_EMPTY = _proof_ctor_neq_empty_binary(
    "FORALL_F_NEQ_EMPTY", "n", "phi", "Forall_f", FORALL_F_AT, _FORALL_F_TAG
)
INSERT_T_NEQ_EMPTY = _proof_ctor_neq_empty_binary(
    "INSERT_T_NEQ_EMPTY", "t1", "t2", "Insert_t", INSERT_T_AT, _INSERT_T_TAG
)
IN_A_NEQ_EMPTY = _proof_ctor_neq_empty_binary(
    "IN_A_NEQ_EMPTY", "t1", "t2", "In_a", IN_A_AT, _IN_A_TAG
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
    "Var_t": _ctor_decl("Var_t", VAR_T_AT, 2, ["v"], _VAR_T_TAG),
    "Eq_f": _ctor_decl("Eq_f", EQ_F_AT, 5, ["t1", "t2"], _EQ_F_TAG),
    "Not_f": _ctor_decl("Not_f", NOT_F_AT, 6, ["phi"], _NOT_F_TAG),
    "Imp_f": _ctor_decl("Imp_f", IMP_F_AT, 7, ["phi1", "phi2"], _IMP_F_TAG),
    "Forall_f": _ctor_decl("Forall_f", FORALL_F_AT, 8, ["n", "phi"], _FORALL_F_TAG),
    "Insert_t": _ctor_decl("Insert_t", INSERT_T_AT, 9, ["t1", "t2"], _INSERT_T_TAG),
    "In_a": _ctor_decl("In_a", IN_A_AT, 10, ["t1", "t2"], _IN_A_TAG),
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

        p.goal(f"!{' '.join(all_vars)}. ~({name1} {args1} = {name2} {args2})")
        p.fix(" ".join(all_vars))
        c1 = SPECL([p._parse(v) for v in fix_vars1], at1)
        c2 = SPECL([p._parse(v) for v in fix_vars2], at2)
        with p.suppose(f"h: {name1} {args1} = {name2} {args2}"):
            inner1 = _ctor_inner_arg(decl1, "1")
            inner2 = _ctor_inner_arg(decl2, "2")
            p.have(
                f"h_po: Pair_ord ({tag1}) ({inner1}) = Pair_ord ({tag2}) ({inner2})"
            ).by_rewrite_of("h", [c1, c2])
            p.have(f"h_inj: ({tag1}) = ({tag2}) /\\ ({inner1}) = ({inner2})").by(
                PAIR_ORD_INJ,
                f"({tag1})",
                f"({inner1})",
                f"({tag2})",
                f"({inner2})",
                "h_po",
            )
            p.have(f"h_tag: ({tag1}) = ({tag2})").by_thm(CONJUNCT1(p.fact("h_inj")))
            # Tag inequality.
            lo, hi = sorted([tag1_idx, tag2_idx])
            tag_neq = _TAG_NEQS[(lo, hi)]
            if tag1_idx < tag2_idx:
                p.have(f"h_tag_neq: ~(({tag1}) = ({tag2}))").by_thm(tag_neq)
                p.absurd().by_conj("h_tag_neq", "h_tag")
            else:
                # _TAG_NEQS is keyed (lo, hi) so the lemma's conclusion
                # is ~(SUC0^lo 0 = SUC0^hi 0); flip to match h_tag.
                from tactics import SYM

                p.have(f"h_tag_sym: ({tag2}) = ({tag1})").by_thm(SYM(p.fact("h_tag")))
                p.have(f"h_tag_neq: ~(({tag2}) = ({tag1}))").by_thm(tag_neq)
                p.absurd().by_conj("h_tag_neq", "h_tag_sym")

    return _THM


# Pairwise disjointness for the 8 non-zero constructors. We expose
# ``CTOR1_NEQ_CTOR2`` for each ordered pair (lexicographic by tag).

_CTOR_NAMES = [
    "Var_t",
    "Eq_f",
    "Not_f",
    "Imp_f",
    "Forall_f",
    "Insert_t",
    "In_a",
]

CTOR_DISJOINTNESS = {}  # (name1, name2) -> theorem
for _i in range(len(_CTOR_NAMES)):
    for _j in range(_i + 1, len(_CTOR_NAMES)):
        _n1, _n2 = _CTOR_NAMES[_i], _CTOR_NAMES[_j]
        CTOR_DISJOINTNESS[(_n1, _n2)] = _proof_ctor_disjoint(
            f"{_n1.upper()}_NEQ_{_n2.upper()}",
            _n1,
            _n2,
        )


# ---------------------------------------------------------------------------
# MONO helpers: per-disjunct iffs for define_wf_lt bodies.
#
# A predicate body for is_term / is_form / free_in / ... is a disjunction
# whose disjuncts have one of two recursive shapes:
#
#   unary:   ?x.   n = C x     /\ f x
#   binary:  ?a b. n = C a b   /\ f a /\ f b
#
# Each shape's f-version equals its g-version when ``f`` and ``g`` agree
# on every k strictly less than n (under nat0_lt). The two helpers below
# produce that per-disjunct iff as a kernel theorem; the outer MONO
# equality is then ``OR_CONG``-chained over the per-disjunct results
# (plus REFL for non-recursive disjuncts), instead of a single 200-line
# nested case-analysis.
#
# The shape of a helper call is:
#   step = mono_iff_unary_step(C, NAT0_LT_C, p.fact("h"))
#   p.have("e: ...").by_thm(step)
# inside an outer @proof whose hypothesis is
#   h : |- !k. nat0_lt k n ==> f k = g k.
# ---------------------------------------------------------------------------


def _extract_nfg(hyp_th):
    """Pull n, f, g out of |- !k. nat0_lt k n ==> f k = g k."""
    forall_pred = dest_forall(hyp_th._concl)
    if forall_pred is None:
        raise ValueError(f"_extract_nfg: hyp_th not !k. ...; got {hyp_th._concl}")
    imp_parts = dest_imp(forall_pred.body)
    if imp_parts is None:
        raise ValueError(
            f"_extract_nfg: hyp body not implication; got {forall_pred.body}"
        )
    ant, conseq = imp_parts
    n_t = rand(ant)  # nat0_lt k n
    fk, gk = dest_eq(conseq)
    return n_t, rator(fk), rator(gk), forall_pred.bvar.ty


def mono_iff_unary_step(ctor, size_lemma, hyp_th):
    """Per-disjunct iff for a unary recursive case.

    Args:
      ctor       : term, type ``nat0 -> nat0`` (e.g. ``Succ_t``).
      size_lemma : ``|- !x. nat0_lt x (ctor x)``.
      hyp_th     : ``|- !k. nat0_lt k n ==> f k = g k`` (the MONO hypothesis).

    Returns:
      ``|- (?x. n = ctor x /\\ f x) = (?x. n = ctor x /\\ g x)``
    where n, f, g are read from ``hyp_th``.
    """
    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    x_var = Var("x", k_ty)
    n_eq_ctor_x = mk_eq(n_t, mk_app(ctor, x_var))
    body_l = mk_and(n_eq_ctor_x, mk_app(f_t, x_var))
    body_r = mk_and(n_eq_ctor_x, mk_app(g_t, x_var))
    pred_l = mk_abs(x_var, body_l)
    pred_r = mk_abs(x_var, body_r)
    LHS = mk_exists(x_var, body_l)
    RHS = mk_exists(x_var, body_r)

    # Forward: {LHS} |- RHS.
    chosen_l = CHOOSE_WITNESS(pred_l, ASSUME(LHS))  # {LHS} |- n = ctor w /\ f w
    n_eq_l = CONJUNCT1(chosen_l)
    fw_th = CONJUNCT2(chosen_l)
    w_t = rand(n_eq_l._concl)  # ctor w; we just need w
    # Strip the ctor to get w itself (= rand of ctor w).
    w_t = rand(w_t)
    sl_at_w = SPEC(w_t, size_lemma)  # |- nat0_lt w (ctor w)
    lt_w_n = REWRITE_RULE([SYM(n_eq_l)], sl_at_w)  # {LHS} |- nat0_lt w n
    fw_eq_gw = MP(SPEC(w_t, hyp_th), lt_w_n)  # {LHS} |- f w = g w
    gw_th = EQ_MP(fw_eq_gw, fw_th)  # {LHS} |- g w
    R_th = EXISTS(pred_r, w_t, CONJ(n_eq_l, gw_th))  # {LHS} |- RHS

    # Reverse: {RHS} |- LHS.  Same shape, swap f <-> g via SYM.
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
    """Per-disjunct iff for a binary recursive case.

    Args:
      ctor          : term, type ``nat0 -> nat0 -> nat0`` (e.g. ``Plus_t``).
      size_lemma_l  : ``|- !a b. nat0_lt a (ctor a b)``.
      size_lemma_r  : ``|- !a b. nat0_lt b (ctor a b)``.
      hyp_th        : ``|- !k. nat0_lt k n ==> f k = g k``.

    Returns:
      ``|- (?a b. n = ctor a b /\\ f a /\\ f b)
            = (?a b. n = ctor a b /\\ g a /\\ g b)``
    where n, f, g are read from ``hyp_th``.
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
        """Prove {src} |- ?a b. target_inner_body, where target_inner_body
        is body_inner_r when src=LHS (fwd) or body_inner_l when src=RHS (rev).
        ``swap_fg=True`` flips f<->g via SYM on the per-arg eq."""
        h_top = ASSUME(src)
        # Outer choose: bind a := w_a.
        outer_pred = dest_exists(src)
        chosen_outer = CHOOSE_WITNESS(outer_pred, h_top)  # |- ?b. body[w_a, b]
        # Inner choose: bind b := w_b. The new inner pred's `a` slot
        # has already been substituted to the outer SELECT, so re-read
        # it from chosen_outer's concl.
        new_inner_pred = dest_exists(chosen_outer._concl)
        chosen_inner = CHOOSE_WITNESS(new_inner_pred, chosen_outer)
        # chosen_inner : {src} |- (n = ctor w_a w_b) /\ (h_a /\ h_b)
        n_eq_th = CONJUNCT1(chosen_inner)
        rest = CONJUNCT2(chosen_inner)
        ha_th = CONJUNCT1(rest)
        hb_th = CONJUNCT2(rest)
        ctor_app = rand(n_eq_th._concl)
        w_b = rand(ctor_app)
        w_a = rand(rator(ctor_app))
        # Size lemmas at (w_a, w_b).
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
        # Re-existentialise: inner pred is target body with a := w_a (so b
        # is the only remaining bvar); outer pred is the result of inner
        # quantification with a still free, which we then bind to w_a.
        # Build via INST'd term shapes:
        target_outer_pred_body = mk_abs(a_var, mk_exists(b_var, target_inner_body))
        # EXISTS at b := w_b: substitutes b in target_inner_pred_body.
        # But we need substitution of a := w_a too; do it by picking the
        # right pred shape. EXISTS only substitutes the bvar of the
        # supplied Abs, so use a transient pred with `a := w_a`.
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
        outer_th = EXISTS(target_outer_pred_body, w_a, inner_th)
        return outer_th

    R_th = _direction(LHS, body_inner_r, swap_fg=False)
    L_th = _direction(RHS, body_inner_l, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def mono_iff_binary_right_step(ctor, size_lemma_r, hyp_th):
    """Per-disjunct iff for a binary disjunct where ONLY the right argument
    feeds back into the recursive predicate (e.g. ``Forall_f v phi /\\ f phi``,
    where ``v`` is a bound-variable index that doesn't recurse).

    Args:
      ctor          : term, type ``nat0 -> nat0 -> nat0`` (e.g. ``Forall_f``).
      size_lemma_r  : ``|- !a b. nat0_lt b (ctor a b)``.
      hyp_th        : ``|- !k. nat0_lt k n ==> f k = g k``.

    Returns:
      ``|- (?a b. n = ctor a b /\\ f b) = (?a b. n = ctor a b /\\ g b)``
    where n, f, g are read from ``hyp_th``.
    """
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
        if swap_fg:
            hb_out = EQ_MP(SYM(eq_b), hb_th)
        else:
            hb_out = EQ_MP(eq_b, hb_th)
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
        outer_th = EXISTS(target_outer_pred_body, w_a, inner_th)
        return outer_th

    R_th = _direction(LHS, body_inner_r, swap_fg=False)
    L_th = _direction(RHS, body_inner_l, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


# ---------------------------------------------------------------------------
# Pointwise MONO helpers for function-valued recursion (free_in, substitute).
#
# When the recursion target type is ``A = nat0 -> bool`` (or any function
# type), the body is ``\v. <bool disjunction over n with f x v references>``.
# The MONO obligation
#   |- (!k. nat0_lt k n ==> f k = g k) ==> F f n = F g n
# is a function-equality. We prove it pointwise: for an arbitrary ``v``,
# build per-disjunct iffs at the bool level using the helpers below, chain
# via ``or_chain_collapse``, generalize with ``GEN(v)``, lift via
# ``FUN_EXT`` to the function equality, then ``by_unfold`` through the
# helper-constant DEF to bridge to ``F f n = F g n``.
#
# Each helper takes the same ``hyp_th`` (function-eq form) and an extra
# ``v_term`` to apply at the bool-result level via ``AP_THM``.
# ---------------------------------------------------------------------------


def mono_iff_unary_pw_step(ctor, size_lemma, hyp_th, v_term):
    """For ``f, g : nat0 -> nat0 -> bool`` and a fixed ``v``, prove
    ``(?x. n = ctor x /\\ f x v) = (?x. n = ctor x /\\ g x v)``.
    """
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
    fw_v_eq_gw_v = AP_THM(fw_eq_gw, v_term)
    gxv_th = EQ_MP(fw_v_eq_gw_v, fxv_th)
    R_th = EXISTS(pred_r, w_t, CONJ(n_eq_l, gxv_th))

    chosen_r = CHOOSE_WITNESS(pred_r, ASSUME(RHS))
    n_eq_r = CONJUNCT1(chosen_r)
    gxv2_th = CONJUNCT2(chosen_r)
    w2_t = rand(rand(n_eq_r._concl))
    sl_at_w2 = SPEC(w2_t, size_lemma)
    lt_w2_n = REWRITE_RULE([SYM(n_eq_r)], sl_at_w2)
    fw2_eq_gw2 = MP(SPEC(w2_t, hyp_th), lt_w2_n)
    fw2_v_eq_gw2_v = AP_THM(fw2_eq_gw2, v_term)
    fxv2_th = EQ_MP(SYM(fw2_v_eq_gw2_v), gxv2_th)
    L_th = EXISTS(pred_l, w2_t, CONJ(n_eq_r, fxv2_th))

    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def _mono_iff_binary_pw_step(
    ctor, size_lemma_l, size_lemma_r, hyp_th, v_term, rest_builder, recurses_l
):
    """Generic binary pointwise step.

    ``rest_builder(fn_t, a, b, v)`` returns the term plugged in as the
    second conjunct of the disjunct (after ``n = ctor a b /\\ ...``).
    ``recurses_l`` says whether the helper should derive ``f a = g a`` (in
    addition to ``f b = g b``); set ``False`` for right-only cases.
    """
    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    a_var = Var("a", k_ty)
    b_var = Var("b", k_ty)

    def _bodies(fn):
        ctor_ab = mk_app(ctor, a_var, b_var)
        return mk_and(
            mk_eq(n_t, ctor_ab),
            rest_builder(fn, a_var, b_var, v_term),
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
        ctor_app = rand(n_eq_th._concl)
        w_b = rand(ctor_app)
        w_a = rand(rator(ctor_app))
        rewrites = []
        if recurses_l:
            sl_a = SPEC(w_b, SPEC(w_a, size_lemma_l))
            lt_a_n = REWRITE_RULE([SYM(n_eq_th)], sl_a)
            eq_a = MP(SPEC(w_a, hyp_th), lt_a_n)
            eq_a_v = AP_THM(eq_a, v_term)
            rewrites.append(eq_a_v)
        sl_b = SPEC(w_b, SPEC(w_a, size_lemma_r))
        lt_b_n = REWRITE_RULE([SYM(n_eq_th)], sl_b)
        eq_b = MP(SPEC(w_b, hyp_th), lt_b_n)
        eq_b_v = AP_THM(eq_b, v_term)
        rewrites.append(eq_b_v)
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
        outer_th = EXISTS(target_outer_pred_body, w_a, inner_th)
        return outer_th

    R_th = _direction(LHS, body_inner_r, swap_fg=False)
    L_th = _direction(RHS, body_inner_l, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def mono_iff_binary_disj_pw_step(ctor, size_lemma_l, size_lemma_r, hyp_th, v_term):
    """``(?a b. n = ctor a b /\\ (f a v \\/ f b v))
    = (?a b. n = ctor a b /\\ (g a v \\/ g b v))``."""
    return _mono_iff_binary_pw_step(
        ctor,
        size_lemma_l,
        size_lemma_r,
        hyp_th,
        v_term,
        rest_builder=lambda fn, a, b, v: mk_or(mk_app(fn, a, v), mk_app(fn, b, v)),
        recurses_l=True,
    )


def mono_iff_forall_pw_step(size_lemma_r, hyp_th, v_term):
    """``(?a b. n = Forall_f a b /\\ ~(v = a) /\\ f b v)
        = (?a b. n = Forall_f a b /\\ ~(v = a) /\\ g b v)``.

    The ``a`` slot is the bound-variable index of the encoded universal;
    only the body slot ``b`` recurses through ``f``."""
    return _mono_iff_binary_pw_step(
        Forall_f,
        None,
        size_lemma_r,
        hyp_th,
        v_term,
        rest_builder=lambda fn, a, b, v: mk_and(mk_not(mk_eq(v, a)), mk_app(fn, b, v)),
        recurses_l=False,
    )


def mono_iff_eq_or_pw_step(ctor, size_lemma_r, hyp_th, v_term):
    """``(?a b. n = ctor a b /\\ (v = a \\/ f b v))
        = (?a b. n = ctor a b /\\ (v = a \\/ g b v))``.

    Used for list-membership-style recursion ``mem_l p x  :=
    ?h t. p = cons_l h t /\\ (x = h \\/ mem_l t x)``: the head slot ``a``
    is non-recursive (just an equality test against the query value),
    only the tail slot ``b`` recurses through ``f``."""
    return _mono_iff_binary_pw_step(
        ctor,
        None,
        size_lemma_r,
        hyp_th,
        v_term,
        rest_builder=lambda fn, a, b, v: mk_or(mk_eq(v, a), mk_app(fn, b, v)),
        recurses_l=False,
    )


# ---------------------------------------------------------------------------
# Value-shape pointwise MONO helpers (for ``substitute``-style recursion).
#
# When the recursion target type is ``A = nat0 -> nat0 -> nat0`` (or any
# function type returning a value rather than a bool), the body has the
# SELECT shape ``\new_t v. @r. <disjunction over r-values>``. Each
# r-value disjunct's "rest" is ``r = ctor_value(... f x args ...)`` --
# the f-call lives buried inside a value-builder on the RHS of an
# equation, not as a bool conjunct.
#
# These helpers prove the per-disjunct iff at the bool level (with r,
# new_t, v as free variables); the outer MONO proof ABSes over r,
# AP_TERMs through the SELECT, ABSes over v and new_t, and finally
# unfolds through the helper-constant DEF.
#
# Each helper applies an ``AP_THM`` chain over ``args`` to lift the
# function-eq ``f w = g w`` to ``f w args1 ... argsk = g w args1 ... argsk``
# and then ``REWRITE_RULE`` substitutes the f-call inside the rest's RHS.
# ---------------------------------------------------------------------------


def _ap_thm_chain(eq_th, args):
    """``|- f w = g w`` plus ``args = [a1, ..., ak]`` -> ``|- f w a1...ak = g w a1...ak``."""
    out = eq_th
    for arg in args:
        out = AP_THM(out, arg)
    return out


def mono_iff_value_unary_pw_step(ctor, size_lemma, hyp_th, args, r_term, value_fn):
    """Per-disjunct iff for a unary value-shape disjunct.

    Args:
      ctor       : term, type ``nat0 -> nat0`` (e.g. ``Succ_t``).
      size_lemma : ``|- !x. nat0_lt x (ctor x)``.
      hyp_th     : ``|- !k. nat0_lt k n ==> f k = g k`` (function eq).
      args       : list of extra argument terms applied to ``f`` / ``g``.
      r_term     : the SELECT-bound result variable (free in the result).
      value_fn   : Python callable taking one term and returning the value
                   term (e.g. ``lambda t: mk_app(Succ_t, t)``).

    Returns:
      ``|- (?x. n = ctor x /\\ r = value_fn(f x args))
            = (?x. n = ctor x /\\ r = value_fn(g x args))``.
    """
    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    x_var = Var("x", k_ty)
    n_eq_ctor_x = mk_eq(n_t, mk_app(ctor, x_var))

    def _body(fn):
        f_call = mk_app(fn, x_var, *args)
        return mk_and(n_eq_ctor_x, mk_eq(r_term, value_fn(f_call)))

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
        fw_args_eq = _ap_thm_chain(fw_eq_gw, args)
        if swap_fg:
            fw_args_eq = SYM(fw_args_eq)
        new_val_eq = REWRITE_RULE([fw_args_eq], val_eq_th)
        new_body = CONJ(n_eq_th, new_val_eq)
        return EXISTS(target_pred, w_t, new_body)

    R_th = _direction(pred_l, LHS, pred_r, swap_fg=False)
    L_th = _direction(pred_r, RHS, pred_l, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def _mono_iff_value_binary_pw_step(
    ctor, size_lemma_l, size_lemma_r, hyp_th, args, rest_builder, recurses_l
):
    """Generic binary value-shape pointwise step.

    ``rest_builder(fn, a, b, args)`` returns the rest term plugged in
    after ``n = ctor a b /\\ ...``; it may freely use
    ``mk_app(fn, a, *args)`` and ``mk_app(fn, b, *args)`` -- the helper
    derives ``f a args = g a args`` and ``f b args = g b args`` and
    ``REWRITE_RULE``s with them. ``recurses_l`` flips off the left-arg
    rewrite (e.g. for ``Forall_f`` whose ``a`` slot is a bound-variable
    index, not a recursive subterm).
    """
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
            eq_a = MP(SPEC(w_a, hyp_th), lt_a_n)
            rewrites.append(_ap_thm_chain(eq_a, args))
        sl_b = SPEC(w_b, SPEC(w_a, size_lemma_r))
        lt_b_n = REWRITE_RULE([SYM(n_eq_th)], sl_b)
        eq_b = MP(SPEC(w_b, hyp_th), lt_b_n)
        rewrites.append(_ap_thm_chain(eq_b, args))
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
        outer_th = EXISTS(target_outer_pred_body, w_a, inner_th)
        return outer_th

    R_th = _direction(LHS, body_inner_r, g_t, swap_fg=False)
    L_th = _direction(RHS, body_inner_l, f_t, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def mono_iff_value_binary_pw_step(
    ctor, size_lemma_l, size_lemma_r, hyp_th, args, r_term, value_fn
):
    """``(?a b. n = ctor a b /\\ r = value_fn(f a args, f b args))
        = (?a b. n = ctor a b /\\ r = value_fn(g a args, g b args))``.

    ``value_fn(a_term, b_term)`` builds the value -- typically
    ``lambda a, b: mk_app(ctor, a, b)``.
    """
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


def mono_iff_forall_value_pw_step(size_lemma_r, hyp_th, args, r_term, v_for_eq):
    """Per-disjunct iff for the ``Forall_f`` value disjunct.

    Body shape (LHS):
      ``?a b. n = Forall_f a b /\\
              ((v_for_eq = a /\\ r = Forall_f a b) \\/
               (~(v_for_eq = a) /\\ r = Forall_f a (f b args)))``.

    Only ``b`` recurses; the ``v_for_eq = a`` ``then`` branch has no
    f-reference.
    """
    return _mono_iff_value_binary_pw_step(
        Forall_f,
        None,
        size_lemma_r,
        hyp_th,
        args,
        rest_builder=lambda fn, a, b, ags: mk_or(
            mk_and(mk_eq(v_for_eq, a), mk_eq(r_term, mk_app(Forall_f, a, b))),
            mk_and(
                mk_not(mk_eq(v_for_eq, a)),
                mk_eq(r_term, mk_app(Forall_f, a, mk_app(fn, b, *ags))),
            ),
        ),
        recurses_l=False,
    )


def _select_collapse_eq(K_t, r_var):
    """``|- (@r. r = K) = K`` for ``K`` not mentioning ``r``.

    One-shot SELECT_AX derivation at predicate ``\\r. r = K`` with
    witness ``K``.
    """
    pred = mk_abs(r_var, mk_eq(r_var, K_t))
    sel_ax_at = INST_TYPE([(r_var.ty, aty)], SELECT_AX)
    spec_p = SPEC(pred, sel_ax_at)  # |- !x. P x ==> P (@P)
    spec_x = SPEC(K_t, spec_p)  # |- P K ==> P (@P)
    p_at_K = mk_app(pred, K_t)
    bridge_K = BETA_CONV(p_at_K)  # |- P K = (K = K)
    p_K_th = EQ_MP(SYM(bridge_K), REFL(K_t))  # |- P K
    p_at_select = MP(spec_x, p_K_th)  # |- P (@P)
    sel_t = mk_select(r_var, mk_eq(r_var, K_t))
    bridge_sel = BETA_CONV(mk_app(pred, sel_t))  # |- P (@P) = ((@P) = K)
    return EQ_MP(bridge_sel, p_at_select)  # |- (@r. r = K) = K


# ---------------------------------------------------------------------------
# Constructor recursion-equation derivation.
#
# Given a recursive predicate F : nat0 -> bool defined via define_wf_lt
# with REC of shape ``|- !n. F n = body[F, n]``, where each body disjunct
# has one of the q-syntax shapes:
#
#   (n = K)                                  -- nullary base (e.g. Empty_t)
#   (?x. n = C x /\ F x)                     -- unary recursive
#   (?x. n = C x)                            -- unary non-recursive (Var_t)
#   (?a b. n = C a b /\ F a /\ F b)          -- binary recursive
#
# ``derive_rec_eq(REC, target_ctor_name, var_names)`` produces the
# constructor recursion equation
#   |- !v1...vk. F (target_C v1...vk) = <recursive call(s)>.
#
# It walks the body, classifies each disjunct by its head constructor,
# applies the appropriate disjointness lemma to non-matching disjuncts
# (collapsing them to F via EQF_INTRO), and uses the matching ctor's
# _INJ to extract a one-point form for the matching disjunct. The
# results are glued via ``or_chain_collapse`` (drops F-disjuncts).
# ---------------------------------------------------------------------------


# Lookup tables: NEQ_EMPTY and INJ lemmas indexed by constructor name.
_CTOR_NEQ_EMPTY = {
    "Var_t": VAR_T_NEQ_EMPTY,
    "Eq_f": EQ_F_NEQ_EMPTY,
    "Not_f": NOT_F_NEQ_EMPTY,
    "Imp_f": IMP_F_NEQ_EMPTY,
    "Forall_f": FORALL_F_NEQ_EMPTY,
    "Insert_t": INSERT_T_NEQ_EMPTY,
    "In_a": IN_A_NEQ_EMPTY,
}
_CTOR_INJ = {
    "Var_t": VAR_T_INJ,
    "Not_f": NOT_F_INJ,
    "Eq_f": EQ_F_INJ,
    "Imp_f": IMP_F_INJ,
    "Forall_f": FORALL_F_INJ,
    "Insert_t": INSERT_T_INJ,
    "In_a": IN_A_INJ,
}


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


def _disjunct_ctor_name(disj):
    """Identify the head constructor named in a body disjunct.

    Recognises:
      - ``n = Empty_t`` -> "Empty_t"
      - ``?args. n = C args (/\\ ...)`` -> name of C (looked up in _CTORS).
    Returns the ctor name, plus the tail of the dest_exists chain (the
    inner conjunction body or the bare equation).
    """
    cur = disj
    while True:
        ex_pred = dest_exists(cur)
        if ex_pred is None:
            break
        cur = ex_pred.body
    # cur is now `n = C args` or `n = C args /\ ...`.
    eq_tm = dest_conj(cur)[0] if not is_eq(cur) else cur
    rhs = dest_eq(eq_tm)[1]
    # Walk left through Comb chains until we hit the constant.
    head = rhs
    while not isinstance(head, type(mk_const("0", []))):
        if hasattr(head, "fun"):
            head = head.fun
        else:
            break
    if not hasattr(head, "name"):
        raise ValueError(f"_disjunct_ctor_name: cannot pin down constructor in {disj}")
    return head.name


def _disjunct_eq_F_via_neq(disj, neq_lemma_dir, target_args):
    """Prove ``|- disj = F`` for a non-matching disjunct.

    ``disj`` is one of:
      ``e1 = K``                                  (no quantifiers, K nullary)
      ``?x. e1 = D x (/\\ R(x))``                 (unary D ≠ target)
      ``?a b. e1 = D a b /\\ R(a, b)``            (binary D ≠ target)
    Witnesses for D's args are extracted from the post-CHOOSE_WITNESS
    body so any outer-bound substitution is already applied (avoids
    free-var capture across nested existentials).
    """
    if is_eq(disj):
        neq_specd = _spec_neq_at(neq_lemma_dir, target_args, [])
        # EQF_INTRO produces |- F = p; flip via SYM for our |- disj = F shape.
        return SYM(EQF_INTRO(neq_specd))
    # Existential: peel binders, extract D's args from the head equation.
    th = ASSUME(disj)
    while dest_exists(th._concl) is not None:
        th = CHOOSE_WITNESS(dest_exists(th._concl), th)
    head_eq_th = th if is_eq(th._concl) else CONJUNCT1(th)
    head_app = dest_eq(head_eq_th._concl)[1]
    other_args = _spine_args(head_app)
    neq_specd = _spec_neq_at(neq_lemma_dir, target_args, other_args)
    F_th = MP(NOT_ELIM(neq_specd), head_eq_th)  # {disj} |- F
    rev = CONTR(disj, ASSUME(F))  # {F} |- disj
    # DEDUCT_ANTISYM_RULE(t1, t2) yields t1._concl = t2._concl.
    return DEDUCT_ANTISYM_RULE(rev, F_th)


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


def _disjunct_eq_match_unary(disj, target_app, target_arg, inj_lemma):
    """Matching unary disjunct: prove ``|- disj = F target_arg`` (or the
    body in the no-recursion case).

    ``disj`` is ``?x. target_app = C x /\\ R(x)`` or ``?x. target_app = C x``
    where ``C`` is target_app's head.  ``inj_lemma`` is the constructor's
    _INJ (``!a b. C a = C b ==> a = b``).  ``target_arg`` is the single
    argument of target_app.

    Returns equation whose RHS is ``R(target_arg)`` (or T if no body).
    """
    ex_pred = dest_exists(disj)
    if ex_pred is None:
        raise ValueError("_disjunct_eq_match_unary: not existential")
    body = ex_pred.body
    conj = dest_conj(body)
    if conj is None:
        # No-recursion variant: ``?x. target_app = C x``. Witness x:=target_arg
        # via REFL; result is T.
        from tactics import EQT_INTRO

        rev = EXISTS(ex_pred, target_arg, REFL(target_app))  # |- ?x. ...
        return EQT_INTRO(rev)
    head_eq, rest = conj
    # rest = R(x); we want to show this equals R(target_arg).
    # Forward: {disj} |- R(target_arg).
    chosen = CHOOSE_WITNESS(ex_pred, ASSUME(disj))  # {disj} |- target_app = C x /\ R(x)
    head_th = CONJUNCT1(chosen)  # {disj} |- target_app = C x
    rest_th = CONJUNCT2(chosen)  # {disj} |- R(x)
    # SYM head_th: |- C x = target_app. But target_app = C target_arg.
    # Use inj_lemma: C target_arg = C x ==> target_arg = x. From head_th
    # rewritten: C target_arg = C x. So target_arg = x.
    # Determine the witness term used by CHOOSE.
    sel_x = rand(head_th._concl)  # = C x
    x_val = rand(sel_x)  # = x (the SELECT term)
    inj_at = SPECL(
        [target_arg, x_val], inj_lemma
    )  # |- C target_arg = C x ==> target_arg = x
    # head_th : {disj} |- target_app = C x. We have target_app = C target_arg by REFL of target_app.
    # Actually target_app is literally `C target_arg` (same term), so no rewrite needed.
    targ_eq_x = MP(inj_at, head_th)  # {disj} |- target_arg = x
    # Substitute x → target_arg in the rest. Use REWRITE_RULE so this
    # works whether ``rest_th`` is ``f x`` (single app) or a wider shape
    # like ``f x v`` (function-valued recursion at a fixed point).
    rest_at_target = REWRITE_RULE([SYM(targ_eq_x)], rest_th)
    rest_target_term = rest_at_target._concl
    body_th_at_target = CONJ(REFL(target_app), ASSUME(rest_target_term))
    rev = EXISTS(ex_pred, target_arg, body_th_at_target)
    return DEDUCT_ANTISYM_RULE(rev, rest_at_target)


def _disjunct_eq_match_binary(disj, target_app, target_args, inj_lemma):
    """Matching binary disjunct: prove ``|- disj = R(target_args)``.

    ``disj`` is ``?a b. target_app = C a b /\\ R(a, b)`` (body is a single
    /\\, R may itself be a conjunction). ``inj_lemma`` is the binary
    _INJ: ``!a1 a2 b1 b2. C a1 b1 = C a2 b2 ==> (a1 = a2 /\\ b1 = b2)``.
    """
    a_t, b_t = target_args
    out_a_pred = dest_exists(disj)
    in_b_pred = dest_exists(out_a_pred.body)
    # Forward: {disj} |- rest[a_t/a, b_t/b].
    chosen_a = CHOOSE_WITNESS(out_a_pred, ASSUME(disj))
    new_inner_pred = dest_exists(chosen_a._concl)
    chosen_ab = CHOOSE_WITNESS(new_inner_pred, chosen_a)
    head_th = CONJUNCT1(chosen_ab)
    rest_th = CONJUNCT2(chosen_ab)
    ctor_app = rand(head_th._concl)
    wb = rand(ctor_app)
    wa = rand(rator(ctor_app))
    inj_at = SPECL([a_t, b_t, wa, wb], inj_lemma)
    pair = MP(inj_at, head_th)  # {disj} |- a_t = wa /\ b_t = wb
    eq_a = CONJUNCT1(pair)
    eq_b = CONJUNCT2(pair)
    rest_at_target = REWRITE_RULE([SYM(eq_a), SYM(eq_b)], rest_th)
    rest_target_term = rest_at_target._concl
    # Reverse: build target body `?a. ?b. body` by EXISTS at b:=b_t then a:=a_t.
    # EXISTS only substitutes its predicate's bvar; the inner pred still
    # references `a` (the outer bvar) free, so substitute a:=a_t first.
    in_b_pred_at_a = mk_abs(
        in_b_pred.bvar,
        vsubst([(a_t, out_a_pred.bvar)])(in_b_pred.body),
    )
    inner_at_target = CONJ(REFL(target_app), ASSUME(rest_target_term))
    inner_th = EXISTS(in_b_pred_at_a, b_t, inner_at_target)
    outer_th = EXISTS(out_a_pred, a_t, inner_th)
    return DEDUCT_ANTISYM_RULE(outer_th, rest_at_target)


from collections import namedtuple

# CtorRegistry: bundles the lookup tables consumed by ``derive_rec_eq``
# and its siblings. Splitting them out from module-level globals lets
# downstream encodings (e.g. PRST) build their own registry without
# mutating ``hf_syntax`` internals.
#
#   ctors       : name -> (name, AT_thm_unused_by_derive, tag_idx_unused,
#                          var_names, tag_str_unused).
#                 ``derive_rec_eq`` consults [0] (name) via _ctor_app and
#                 [3] (var_names) for arity; the other slots are kept for
#                 compatibility with the hf-side constructor-prep code.
#   inj         : name -> ``|- !args. C args1 = C args2 ==> args1 = args2``.
#   disjointness: (a_name, b_name) -> ``|- !ax bx. ~(C_a ax = C_b bx)``.
#   neq_empty   : name -> ``|- !args. ~(C args = empty_const)``.
#   empty_name  : the string name of the "zero" constant (e.g. "Empty_t",
#                 "Empty_pt") that gets special-cased through neq_empty
#                 rather than the pairwise table.
CtorRegistry = namedtuple(
    "CtorRegistry", ["ctors", "inj", "disjointness", "neq_empty", "empty_name"]
)


# Default registry: the hf-side constructors.
HF_REGISTRY = CtorRegistry(
    ctors=_CTORS,
    inj=_CTOR_INJ,
    disjointness=CTOR_DISJOINTNESS,
    neq_empty=_CTOR_NEQ_EMPTY,
    empty_name="Empty_t",
)


def _ctor_neq_lemma(ctor_a_name, ctor_b_name, registry=None):
    """Look up ``|- !args1 args2. ~(ctor_a args1 = ctor_b args2)`` in
    ``registry`` (defaults to the hf-side registry)."""
    if registry is None:
        registry = HF_REGISTRY
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
    """Specialise the disjointness lemma at concrete args.

    ``neq_lemma_dir = ("fwd"|"rev", thm)``. ``"fwd"`` means the lemma
    has shape ``!aArgs bArgs. ~(A aArgs = B bArgs)``; ``"rev"`` means
    args are swapped (we'll SYM the conclusion).  Returns
    ``|- ~(A ctor_a_args = B ctor_b_args)``.
    """
    direction, lemma = neq_lemma_dir
    if direction == "fwd":
        return SPECL(ctor_a_args + ctor_b_args, lemma)
    # rev: lemma is ~(B b = A a); we want ~(A a = B b). Use NE_SYM-style.
    swapped = SPECL(ctor_b_args + ctor_a_args, lemma)
    # ~(B b = A a) -> ~(A a = B b).
    from tactics import NE_SYM

    return NE_SYM(swapped)


def _ctor_app(ctor_decl, args):
    """Build the term ``C a1 ... ak`` for a constructor entry."""
    name = ctor_decl[0]
    return mk_app(mk_const(name, []), *args)


def derive_rec_eq(REC, target_ctor_name, var_names, *, registry=None):
    """Constructor recursion equation, auto-generated.

    Args:
      REC : ``|- !n. F n = body[F, n]`` from ``define_wf_lt``.
      target_ctor_name : name in ``registry.ctors`` (e.g. ``"Succ_t"``).
      var_names : list of strings naming the constructor's args
                  (length must match the constructor's arity).
      registry  : ``CtorRegistry`` to consult; defaults to the hf-side
                  registry. Pass a custom registry to derive recursion
                  equations against a different set of constructors.

    Returns:
      ``|- !v1...vk. F (target_C v1...vk) = <body of matching disjunct,
                                              with v1..vk substituted>``,
      with all non-matching disjuncts collapsed to F via disjointness.
    """
    if registry is None:
        registry = HF_REGISTRY
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
    body_at = rand(rec_at._concl)
    disjuncts = _split_n_disj(body_at)

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

    body_eq = or_chain_collapse(per_eqs)
    final = TRANS(rec_at, body_eq)
    return GENL(target_args, final)


def derive_rec_eq_pw(REC, target_ctor_name, var_names, *, registry=None):
    """Pointwise constructor recursion for function-valued recursion.

    Given REC : ``|- !n. fn n = (\\v. body[fn, n, v])`` from
    ``define_wf_lt`` (where the body is a disjunction whose disjuncts
    follow the q-syntax shapes parameterised by ``v``), produce
        ``|- !v1...vk v. fn (C v1...vk) v = <matching-disjunct collapsed>``.

    Same dispatch logic as ``derive_rec_eq``: match the body's disjunct
    against the target via INJ, collapse the rest via disjointness for
    non-matching disjuncts. The only delta is the AP_THM(v) +
    BETA_CONV step that lifts the function-equality REC to a bool eq
    before the disjunction is processed.
    """
    if registry is None:
        registry = HF_REGISTRY
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
    body_abs = rand(rec_at._concl)
    v_bvar = body_abs.bvar
    rec_at_v = AP_THM(rec_at, v_bvar)
    rhs_redex = rand(rec_at_v._concl)
    rhs_beta = BETA_CONV(rhs_redex)
    rec_normalized = TRANS(rec_at_v, rhs_beta)

    body_at = rand(rec_normalized._concl)
    disjuncts = _split_n_disj(body_at)
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
    body_eq = or_chain_collapse(per_eqs)
    final = TRANS(rec_normalized, body_eq)
    return GENL(target_args + [v_bvar], final)


def _disjunct_eq_match_nullary(disj, target_app):
    """Matching nullary disjunct: ``disj`` is ``target_app = K /\\ R``
    where ``K = target_app`` (head is REFL). Returns ``|- disj = R``.
    """
    parts = dest_conj(disj)
    if parts is None:
        raise ValueError("_disjunct_eq_match_nullary: not a conjunction")
    _head_eq, rest = parts
    rest_th = CONJUNCT2(ASSUME(disj))  # {disj} |- rest
    disj_th = CONJ(REFL(target_app), ASSUME(rest))  # {rest} |- disj
    return DEDUCT_ANTISYM_RULE(disj_th, rest_th)


def derive_rec_eq_select(
    REC, target_ctor_name, var_names, extra_arg_vars, *, registry=None
):
    """Constructor recursion equation for SELECT-shaped recursion.

    Given REC : ``|- !n. fn n = (\\arg1...argk. @r. body[fn, n, args, r])``
    from ``define_wf_lt`` (where ``A = type(arg1) -> ... -> nat0`` and the
    body is a disjunction over r-values), produce
        ``|- !v1...vk arg1...argk. fn (C v1...vk) arg1...argk = R``
    where ``R`` is the matching disjunct's r-value (with witnesses
    instantiated to the constructor args).

    Supports nullary constructors via ``target_ctor_name = "Empty_t"`` and
    ``var_names = []``; the matching disjunct is then a non-existential
    conjunction (``Empty_t = Empty_t /\\ rest``). Conditional matched rests
    (``(cond /\\ r = T) \\/ (~cond /\\ r = E)``, used by ``Var_t`` and
    ``Forall_f`` in substitute) need ``derive_rec_eq_select_cond``.
    """
    if registry is None:
        registry = HF_REGISTRY
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

    rec_at = SPEC(target_app, REC)
    # Walk through the curried args via AP_THM + BETA_CONV until we hit
    # the @r. body level.
    cur = rec_at
    for arg in extra_arg_vars:
        cur_app = AP_THM(cur, arg)
        rhs_redex = rand(cur_app._concl)
        rhs_beta = BETA_CONV(rhs_redex)
        cur = TRANS(cur_app, rhs_beta)
    # cur : |- fn target_app arg1...argk = @r. body[fn, target_app, args, r]
    select_term = rand(cur._concl)  # @r. body
    select_pred = select_term.arg  # \r. body  (the predicate of @)
    r_bvar = select_pred.bvar
    body_at = select_pred.body  # body[fn, target_app, args, r]
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
                    "derive_rec_eq_select: matched disjunct did not "
                    f"reduce to ``r = K``; got {rhs}. Conditional cases "
                    "(Var_t / Forall_f) need separate handling."
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

    body_eq = or_chain_collapse(per_eqs)
    # body_eq : |- body[..., r] = (r = K)
    abs_body_eq = ABS(r_bvar, body_eq)
    # abs_body_eq : |- (\r. body) = (\r. r = K)
    sel_const = mk_const("@", [(r_bvar.ty, _aty_for_select())])
    select_eq = AP_TERM(sel_const, abs_body_eq)
    # select_eq : |- (@r. body) = (@r. r = K)
    collapse = _select_collapse_eq(matched_K, r_bvar)
    # collapse : |- (@r. r = K) = K
    select_to_K = TRANS(select_eq, collapse)
    final = TRANS(cur, select_to_K)
    # final : |- fn target_app args = K
    return GENL(target_args + list(extra_arg_vars), final)


def _aty_for_select():
    """The schematic type variable used by SELECT_AX (and mk_select)."""
    return aty


def _conditional_body_eq(P_term, T_val, E_val, r_var, taking_then):
    """Helper for conditional SELECT collapse.

    Body shape: ``(P /\\ r = T) \\/ (~P /\\ r = E)``. Under hypothesis
    ``P`` (or ``~P``), the whole disjunction equals ``r = T`` (or
    ``r = E``).

    Returns:
      taking_then=True : ``{P} |- (P /\\ r = T) \\/ (~P /\\ r = E) = (r = T)``
      taking_then=False: ``{~P} |- (P /\\ r = T) \\/ (~P /\\ r = E) = (r = E)``
    """
    not_P = mk_not(P_term)
    eq_T = mk_eq(r_var, T_val)
    eq_E = mk_eq(r_var, E_val)
    left_conj = mk_and(P_term, eq_T)
    right_conj = mk_and(not_P, eq_E)
    body = mk_or(left_conj, right_conj)

    if taking_then:
        H = ASSUME(P_term)
        body_th = ASSUME(body)
        # Forward case-split: each branch ends in `r = T_val`.
        branch_l = DISCH(left_conj, CONJUNCT2(ASSUME(left_conj)))
        # right branch: ~P contradicts H.
        notP_th = CONJUNCT1(ASSUME(right_conj))
        F_th = MP(NOT_ELIM(notP_th), H)
        branch_r = DISCH(right_conj, CONTR(eq_T, F_th))
        forward = DISJ_CASES(body_th, branch_l, branch_r)
        # Reverse: build the disjunction from `r = T`.
        eq_T_th = ASSUME(eq_T)
        left_th = CONJ(H, eq_T_th)
        reverse = DISJ1(left_th, right_conj)
        return DEDUCT_ANTISYM_RULE(reverse, forward)
    else:
        H = ASSUME(not_P)
        body_th = ASSUME(body)
        # Forward case-split: each branch ends in `r = E_val`.
        P_th = CONJUNCT1(ASSUME(left_conj))
        F_th = MP(NOT_ELIM(H), P_th)
        branch_l = DISCH(left_conj, CONTR(eq_E, F_th))
        branch_r = DISCH(right_conj, CONJUNCT2(ASSUME(right_conj)))
        forward = DISJ_CASES(body_th, branch_l, branch_r)
        # Reverse: DISJ2 right with `r = E`.
        eq_E_th = ASSUME(eq_E)
        right_th = CONJ(H, eq_E_th)
        reverse = DISJ2(left_conj, right_th)
        return DEDUCT_ANTISYM_RULE(reverse, forward)


def derive_rec_eq_select_cond(
    REC, target_ctor_name, var_names, extra_arg_vars, *, registry=None
):
    """Constructor recursion equation for SELECT-shaped recursion with
    a conditional matching disjunct.

    The matched disjunct (after INJ-witness substitution) reduces to
    ``(P /\\ r = T) \\/ (~P /\\ r = E)`` where ``P``, ``T``, ``E`` are
    expressions in the constructor args + extras. Returns the pair
    ``(THEN_TH, ELSE_TH)``:

      THEN_TH : ``|- !v1...vk extras. P  ==> fn (C v1...vk) extras = T``
      ELSE_TH : ``|- !v1...vk extras. ~P ==> fn (C v1...vk) extras = E``
    """
    if registry is None:
        registry = HF_REGISTRY
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

    rec_at = SPEC(target_app, REC)
    cur = rec_at
    for arg in extra_arg_vars:
        cur_app = AP_THM(cur, arg)
        rhs_redex = rand(cur_app._concl)
        rhs_beta = BETA_CONV(rhs_redex)
        cur = TRANS(cur_app, rhs_beta)
    select_term = rand(cur._concl)
    select_pred = select_term.arg
    r_bvar = select_pred.bvar
    body_at = select_pred.body
    disjuncts = _split_n_disj(body_at)

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
                    f"not a disjunction; got {rhs}. Use "
                    "``derive_rec_eq_select`` for non-conditional cases."
                )
            left_conj_t, right_conj_t = disj_parts
            left_parts = dest_conj(left_conj_t)
            right_parts = dest_conj(right_conj_t)
            if left_parts is None or right_parts is None:
                raise ValueError(
                    "derive_rec_eq_select_cond: matched RHS not "
                    "(P /\\ r = T) \\/ (~P /\\ r = E)"
                )
            P_t, eq_T = left_parts
            _not_P_t, eq_E = right_parts
            T_val = dest_eq(eq_T)[1]
            E_val = dest_eq(eq_E)[1]
            matched_form = (P_t, T_val, E_val)
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
    not_P_t = mk_not(P_t)

    def _build_branch(taking_then, K_t, hyp_t):
        cond_eq = _conditional_body_eq(
            P_t, T_val, E_val, r_bvar, taking_then=taking_then
        )
        # cond_eq : {hyp_t} |- ((P /\ r = T) \/ (~P /\ r = E)) = (r = K)
        body_to_eqK = TRANS(body_eq, cond_eq)
        abs_body_eqK = ABS(r_bvar, body_to_eqK)
        select_to_eqK = AP_TERM(sel_const, abs_body_eqK)
        sel_collapse = _select_collapse_eq(K_t, r_bvar)
        select_to_K = TRANS(select_to_eqK, sel_collapse)
        fn_eq_K = TRANS(cur, select_to_K)
        # fn_eq_K : {hyp_t} |- fn target_app extras = K
        return GENL(target_args + list(extra_arg_vars), DISCH(hyp_t, fn_eq_K))

    THEN_TH = _build_branch(True, T_val, P_t)
    ELSE_TH = _build_branch(False, E_val, not_P_t)
    return THEN_TH, ELSE_TH


# ---------------------------------------------------------------------------
# Stage 1 (b): is_term -- "encodes an HF term" predicate.
#
# Body shape:
#   F is_term n  :=
#        n = Empty_t
#     \/ ?x. n = Var_t x
#     \/ ?a b. n = Insert_t a b /\ is_term a /\ is_term b
#
# The body is registered as constant ``_is_term_F`` so the MONO theorem
# can speak about it by name. After ``define_wf_lt`` returns the raw
# REC (``|- !n. is_term n = _is_term_F is_term n``), we unfold the
# helper constant and beta-reduce its application to recover the
# disjunction-shaped REC that ``derive_rec_eq`` consumes.
# ---------------------------------------------------------------------------


_x_n0 = Var("x", nat0_ty)
_a_n0 = Var("a", nat0_ty)
_b_n0 = Var("b", nat0_ty)
_pred_ty = parse_type("nat0 -> bool")
_F_pred_ty = parse_type("(nat0 -> bool) -> nat0 -> bool")
_f_pred = Var("f", _pred_ty)
_n_var_top = Var("n", nat0_ty)


_IS_TERM_F_DEF = define(
    "_is_term_F",
    _F_pred_ty,
    "\\f:nat0->bool. \\n:nat0. "
    "n = Empty_t \\/ "
    "(?x. n = Var_t x) \\/ "
    "(?a b. n = Insert_t a b /\\ f a /\\ f b)",
)
_IS_TERM_F = mk_const("_is_term_F", [])


@proof
def IS_TERM_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
    ==> _is_term_F f n = _is_term_F g n."""
    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> _is_term_F f n = _is_term_F g n",
        types={"f": _pred_ty, "g": _pred_ty, "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")

    h_th = p.fact("h")
    eq_empty = REFL(p._parse("n = Empty_t"))
    eq_var = REFL(p._parse("?x. n = Var_t x"))
    eq_insert = mono_iff_binary_step(
        Insert_t, NAT0_LT_INSERT_T_L, NAT0_LT_INSERT_T_R, h_th
    )
    body_eq = or_chain_collapse([eq_empty, eq_var, eq_insert])

    p.thus("_is_term_F f n = _is_term_F g n").by_unfold(body_eq, _IS_TERM_F_DEF)


def _unfold_rec_via_F_def(rec_raw, F_def):
    """Convert ``|- !n. fn n = F fn n`` to ``|- !n. fn n = body[fn, n]``
    by unfolding the helper constant and beta-reducing its application."""
    forall_pred = dest_forall(rec_raw._concl)
    n_local = forall_pred.bvar
    spec = SPEC(n_local, rec_raw)  # |- fn n = F fn n
    rhs = rand(spec._concl)
    eq_unfold = REWRITE_CONV([F_def], rhs)  # |- F fn n = (\f n. body) fn n
    eq_beta = BETA_NORM(rand(eq_unfold._concl))  # |- (\f n. body) fn n = body[fn, n]
    rhs_eq = TRANS(eq_unfold, eq_beta)  # |- F fn n = body[fn, n]
    return GEN(n_local, TRANS(spec, rhs_eq))


IS_TERM_DEF, _IS_TERM_REC_RAW = define_wf_lt(
    "is_term",
    _pred_ty,
    _IS_TERM_F,
    IS_TERM_MONO,
)
IS_TERM_REC = _unfold_rec_via_F_def(_IS_TERM_REC_RAW, _IS_TERM_F_DEF)


# Constructor recursion equations.
IS_TERM_AT_VAR = derive_rec_eq(IS_TERM_REC, "Var_t", ["v"])
IS_TERM_AT_INSERT = derive_rec_eq(IS_TERM_REC, "Insert_t", ["t1", "t2"])


# ---------------------------------------------------------------------------
# Stage 1 (b): is_form -- "encodes an HF formula" predicate.
#
# Body shape:
#   F is_form n :=
#        ?a b. n = Eq_f a b /\ is_term a /\ is_term b      -- non-recursive in f
#     \/ ?x. n = Not_f x /\ is_form x                       -- unary recursive
#     \/ ?a b. n = Imp_f a b /\ is_form a /\ is_form b      -- binary recursive
#     \/ ?a b. n = Forall_f a b /\ is_form b                -- right-only recursive
#
# Forall_f's "right-only" recursion needs ``mono_iff_binary_right_step``
# (added above): the ``v`` (Var index) slot doesn't feed back into the
# predicate, so the standard binary helper would prove the wrong iff.
# ---------------------------------------------------------------------------


_IS_FORM_F_DEF = define(
    "_is_form_F",
    _F_pred_ty,
    "\\f:nat0->bool. \\n:nat0. "
    "(?a b. n = Eq_f a b /\\ is_term a /\\ is_term b) \\/ "
    "(?x. n = Not_f x /\\ f x) \\/ "
    "(?a b. n = Imp_f a b /\\ f a /\\ f b) \\/ "
    "(?a b. n = Forall_f a b /\\ f b) \\/ "
    "(?a b. n = In_a a b /\\ is_term a /\\ is_term b)",
)
_IS_FORM_F = mk_const("_is_form_F", [])


@proof
def IS_FORM_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
    ==> _is_form_F f n = _is_form_F g n."""
    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> _is_form_F f n = _is_form_F g n",
        types={"f": _pred_ty, "g": _pred_ty, "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")

    h_th = p.fact("h")
    eq_eq = REFL(p._parse("?a b. n = Eq_f a b /\\ is_term a /\\ is_term b"))
    eq_not = mono_iff_unary_step(Not_f, NAT0_LT_NOT_F, h_th)
    eq_imp = mono_iff_binary_step(Imp_f, NAT0_LT_IMP_F_L, NAT0_LT_IMP_F_R, h_th)
    eq_forall = mono_iff_binary_right_step(Forall_f, NAT0_LT_FORALL_F_R, h_th)
    eq_in = REFL(p._parse("?a b. n = In_a a b /\\ is_term a /\\ is_term b"))
    body_eq = or_chain_collapse([eq_eq, eq_not, eq_imp, eq_forall, eq_in])

    p.thus("_is_form_F f n = _is_form_F g n").by_unfold(body_eq, _IS_FORM_F_DEF)


IS_FORM_DEF, _IS_FORM_REC_RAW = define_wf_lt(
    "is_form",
    _pred_ty,
    _IS_FORM_F,
    IS_FORM_MONO,
)
IS_FORM_REC = _unfold_rec_via_F_def(_IS_FORM_REC_RAW, _IS_FORM_F_DEF)


IS_FORM_AT_EQ = derive_rec_eq(IS_FORM_REC, "Eq_f", ["t1", "t2"])
IS_FORM_AT_NOT = derive_rec_eq(IS_FORM_REC, "Not_f", ["phi"])
IS_FORM_AT_IMP = derive_rec_eq(IS_FORM_REC, "Imp_f", ["phi1", "phi2"])
IS_FORM_AT_FORALL = derive_rec_eq(IS_FORM_REC, "Forall_f", ["v", "phi"])
IS_FORM_AT_IN = derive_rec_eq(IS_FORM_REC, "In_a", ["t1", "t2"])


# ---------------------------------------------------------------------------
# Stage 1 (c): free_in -- "variable index v occurs free in encoded n".
#
# Body shape (Empty_t falls through to ``F`` because no disjunct head
# matches it):
#   F free_in n  :=  \v.
#        ?x. n = Var_t x /\ v = x
#     \/ ?a b. n = Eq_f a b /\ (free_in a v \/ free_in b v)
#     \/ ?x. n = Not_f x /\ free_in x v
#     \/ ?a b. n = Imp_f a b /\ (free_in a v \/ free_in b v)
#     \/ ?a b. n = Forall_f a b /\ ~(v = a) /\ free_in b v
#     \/ ?a b. n = Insert_t a b /\ (free_in a v \/ free_in b v)
#     \/ ?a b. n = In_a a b /\ (free_in a v \/ free_in b v)
#
# free_in : nat0 -> (nat0 -> bool); the recursion target type is
# ``A = nat0 -> bool`` so MONO is a function-equality. We prove the body
# pointwise via ``mono_iff_*_pw_step`` helpers (above), GEN over v, and
# FUN_EXT to reach the function form, then ``by_unfold`` through the
# helper-constant DEF.
# ---------------------------------------------------------------------------


_v_n0 = Var("v", nat0_ty)
_pred2_ty = parse_type("nat0 -> nat0 -> bool")
_F_pred2_ty = parse_type("(nat0 -> nat0 -> bool) -> nat0 -> nat0 -> bool")
_f_pred2 = Var("f", _pred2_ty)


_FREE_IN_F_DEF = define(
    "_free_in_F",
    _F_pred2_ty,
    "\\f:nat0->nat0->bool. \\n:nat0. \\v:nat0. "
    "(?x. n = Var_t x /\\ v = x) \\/ "
    "(?a b. n = Eq_f a b /\\ (f a v \\/ f b v)) \\/ "
    "(?x. n = Not_f x /\\ f x v) \\/ "
    "(?a b. n = Imp_f a b /\\ (f a v \\/ f b v)) \\/ "
    "(?a b. n = Forall_f a b /\\ ~(v = a) /\\ f b v) \\/ "
    "(?a b. n = Insert_t a b /\\ (f a v \\/ f b v)) \\/ "
    "(?a b. n = In_a a b /\\ (f a v \\/ f b v))",
)
_FREE_IN_F = mk_const("_free_in_F", [])


@proof
def FREE_IN_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                  ==> _free_in_F f n = _free_in_F g n.

    Function-valued MONO. We prove a pointwise body-equation, GEN/FUN_EXT
    to lift to the lambda equality, then ``by_unfold`` to bridge to the
    helper constant on each side.
    """
    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> _free_in_F f n = _free_in_F g n",
        types={"f": _pred2_ty, "g": _pred2_ty, "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")

    h_th = p.fact("h")

    eq_var = REFL(p._parse("?x. n = Var_t x /\\ v = x"))
    eq_eq = mono_iff_binary_disj_pw_step(
        Eq_f, NAT0_LT_EQ_F_L, NAT0_LT_EQ_F_R, h_th, _v_n0
    )
    eq_not = mono_iff_unary_pw_step(Not_f, NAT0_LT_NOT_F, h_th, _v_n0)
    eq_imp = mono_iff_binary_disj_pw_step(
        Imp_f, NAT0_LT_IMP_F_L, NAT0_LT_IMP_F_R, h_th, _v_n0
    )
    eq_forall = mono_iff_forall_pw_step(NAT0_LT_FORALL_F_R, h_th, _v_n0)
    eq_insert = mono_iff_binary_disj_pw_step(
        Insert_t, NAT0_LT_INSERT_T_L, NAT0_LT_INSERT_T_R, h_th, _v_n0
    )
    eq_in = mono_iff_binary_disj_pw_step(
        In_a, NAT0_LT_IN_A_L, NAT0_LT_IN_A_R, h_th, _v_n0
    )
    body_eq = or_chain_collapse(
        [
            eq_var,
            eq_eq,
            eq_not,
            eq_imp,
            eq_forall,
            eq_insert,
            eq_in,
        ]
    )
    # body_eq : {h_concl} |- body[f, n, v] = body[g, n, v].

    abs_eq = ABS(_v_n0, body_eq)
    # abs_eq : {h_concl} |- (\v. body[f, n, v]) = (\v. body[g, n, v]).

    p.thus("_free_in_F f n = _free_in_F g n").by_unfold(abs_eq, _FREE_IN_F_DEF)


FREE_IN_DEF, _FREE_IN_REC_RAW = define_wf_lt(
    "free_in",
    _pred2_ty,
    _FREE_IN_F,
    FREE_IN_MONO,
)
FREE_IN_REC = _unfold_rec_via_F_def(_FREE_IN_REC_RAW, _FREE_IN_F_DEF)


# Constructor recursion equations (pointwise).
FREE_IN_AT_VAR = derive_rec_eq_pw(FREE_IN_REC, "Var_t", ["w"])
FREE_IN_AT_EQ = derive_rec_eq_pw(FREE_IN_REC, "Eq_f", ["t1", "t2"])
FREE_IN_AT_NOT = derive_rec_eq_pw(FREE_IN_REC, "Not_f", ["phi"])
FREE_IN_AT_IMP = derive_rec_eq_pw(FREE_IN_REC, "Imp_f", ["phi1", "phi2"])
FREE_IN_AT_FORALL = derive_rec_eq_pw(FREE_IN_REC, "Forall_f", ["w", "phi"])
FREE_IN_AT_INSERT = derive_rec_eq_pw(FREE_IN_REC, "Insert_t", ["t1", "t2"])
FREE_IN_AT_IN = derive_rec_eq_pw(FREE_IN_REC, "In_a", ["t1", "t2"])


# ---------------------------------------------------------------------------
# Stage 1 (c): substitute -- replace variable index ``v`` by encoded term
# ``new_t`` inside encoded ``n``.
#
# Result type is ``nat0``; the body is a SELECT (``@r``) over a
# disjunction of constructor cases. Each non-Forall_f, non-Var_t
# disjunct fixes ``r`` to a constructor-specific value; the ``@r``
# picks the unique value when exactly one disjunct fires (which holds
# for any well-formed n).
#
# Body shape:
#   F substitute n  :=  \new_t v.
#       @r.
#            (n = Empty_t /\ r = Empty_t)
#         \/ (?x. n = Var_t x
#                 /\ ((v = x  /\ r = new_t)
#                  \/ (~(v = x) /\ r = Var_t x)))
#         \/ (?a b. n = Eq_f a b
#                 /\ r = Eq_f (sub a new_t v) (sub b new_t v))
#         \/ (?x. n = Not_f x /\ r = Not_f (sub x new_t v))
#         \/ (?a b. n = Imp_f a b
#                 /\ r = Imp_f (sub a new_t v) (sub b new_t v))
#         \/ (?a b. n = Forall_f a b
#                 /\ ((v = a   /\ r = Forall_f a b)
#                  \/ (~(v = a) /\ r = Forall_f a (sub b new_t v))))
#         \/ (?a b. n = Insert_t a b
#                 /\ r = Insert_t (sub a new_t v) (sub b new_t v))
#         \/ (?a b. n = In_a a b
#                 /\ r = In_a (sub a new_t v) (sub b new_t v))
#   where ``sub k new_t v`` is shorthand for ``f k new_t v``.
#
# A : ``nat0 -> nat0 -> nat0`` (curry new_t and v under the recursion target).
#
# Output:
#   * SUBSTITUTE_MONO, SUBSTITUTE_DEF, SUBSTITUTE_REC.
#   * Seven non-conditional rec equations (Empty_t, Eq_f, Not_f, Imp_f,
#     Insert_t, In_a) via ``derive_rec_eq_select``.
#   * Four conditional rec equations for Var_t and Forall_f via
#     ``derive_rec_eq_select_cond`` (each constructor yields a HIT
#     branch ``cond ==> rhs = then_K`` and a MISS branch
#     ``~cond ==> rhs = else_K``).
# ---------------------------------------------------------------------------


_new_t_n0 = Var("new_t", nat0_ty)
_r_n0 = Var("r", nat0_ty)
_pred3_ty = parse_type("nat0 -> nat0 -> nat0 -> nat0")
_F_pred3_ty = parse_type(
    "(nat0 -> nat0 -> nat0 -> nat0) -> nat0 -> nat0 -> nat0 -> nat0"
)
_f_pred3 = Var("f", _pred3_ty)


_SUBSTITUTE_F_DEF = define(
    "_substitute_F",
    _F_pred3_ty,
    "\\f:nat0->nat0->nat0->nat0. \\n:nat0. \\new_t:nat0. \\v:nat0. @r:nat0. "
    "(n = Empty_t /\\ r = Empty_t) \\/ "
    "(?x. n = Var_t x /\\ "
    "((v = x /\\ r = new_t) \\/ (~(v = x) /\\ r = Var_t x))) \\/ "
    "(?a b. n = Eq_f a b /\\ r = Eq_f (f a new_t v) (f b new_t v)) \\/ "
    "(?x. n = Not_f x /\\ r = Not_f (f x new_t v)) \\/ "
    "(?a b. n = Imp_f a b /\\ r = Imp_f (f a new_t v) (f b new_t v)) \\/ "
    "(?a b. n = Forall_f a b /\\ "
    "((v = a /\\ r = Forall_f a b) \\/ "
    "(~(v = a) /\\ r = Forall_f a (f b new_t v)))) \\/ "
    "(?a b. n = Insert_t a b /\\ r = Insert_t (f a new_t v) (f b new_t v)) \\/ "
    "(?a b. n = In_a a b /\\ r = In_a (f a new_t v) (f b new_t v))",
)
_SUBSTITUTE_F = mk_const("_substitute_F", [])


@proof
def SUBSTITUTE_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                  ==> _substitute_F f n = _substitute_F g n.

    Value-valued MONO. Per-disjunct iffs are proved at the
    bool-disjunction-under-@r level using the value-shape pw helpers;
    chained via ``or_chain_collapse``; ``ABS`` over r lifts to lambda
    eq; ``AP_TERM`` over the SELECT constant lifts to SELECT eq;
    ``ABS`` over v then new_t lifts to function eq; ``by_unfold``
    bridges to ``_substitute_F``.
    """
    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> "
        "_substitute_F f n = _substitute_F g n",
        types={"f": _pred3_ty, "g": _pred3_ty, "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")

    h_th = p.fact("h")
    args = [_new_t_n0, _v_n0]

    n_t = p._parse("n")
    eq_empty = REFL(mk_and(mk_eq(n_t, Empty_t), mk_eq(_r_n0, Empty_t)))
    eq_var = REFL(
        mk_exists(
            _x_n0,
            mk_and(
                mk_eq(n_t, mk_app(Var_t, _x_n0)),
                mk_or(
                    mk_and(mk_eq(_v_n0, _x_n0), mk_eq(_r_n0, _new_t_n0)),
                    mk_and(
                        mk_not(mk_eq(_v_n0, _x_n0)), mk_eq(_r_n0, mk_app(Var_t, _x_n0))
                    ),
                ),
            ),
        )
    )
    eq_eq = mono_iff_value_binary_pw_step(
        Eq_f,
        NAT0_LT_EQ_F_L,
        NAT0_LT_EQ_F_R,
        h_th,
        args,
        _r_n0,
        lambda a, b: mk_app(Eq_f, a, b),
    )
    eq_not = mono_iff_value_unary_pw_step(
        Not_f,
        NAT0_LT_NOT_F,
        h_th,
        args,
        _r_n0,
        lambda t: mk_app(Not_f, t),
    )
    eq_imp = mono_iff_value_binary_pw_step(
        Imp_f,
        NAT0_LT_IMP_F_L,
        NAT0_LT_IMP_F_R,
        h_th,
        args,
        _r_n0,
        lambda a, b: mk_app(Imp_f, a, b),
    )
    eq_forall = mono_iff_forall_value_pw_step(
        NAT0_LT_FORALL_F_R,
        h_th,
        args,
        _r_n0,
        _v_n0,
    )
    eq_insert = mono_iff_value_binary_pw_step(
        Insert_t,
        NAT0_LT_INSERT_T_L,
        NAT0_LT_INSERT_T_R,
        h_th,
        args,
        _r_n0,
        lambda a, b: mk_app(Insert_t, a, b),
    )
    eq_in = mono_iff_value_binary_pw_step(
        In_a,
        NAT0_LT_IN_A_L,
        NAT0_LT_IN_A_R,
        h_th,
        args,
        _r_n0,
        lambda a, b: mk_app(In_a, a, b),
    )

    body_eq = or_chain_collapse(
        [
            eq_empty,
            eq_var,
            eq_eq,
            eq_not,
            eq_imp,
            eq_forall,
            eq_insert,
            eq_in,
        ]
    )
    # body_eq : {h_concl} |- body[f, n, new_t, v, r] = body[g, n, new_t, v, r]

    abs_r_eq = ABS(_r_n0, body_eq)
    # abs_r_eq : ... |- (\r. body[f]) = (\r. body[g])
    sel_const = mk_const("@", [(nat0_ty, _aty_for_select())])
    select_eq = AP_TERM(sel_const, abs_r_eq)
    # select_eq : ... |- (@r. body[f]) = (@r. body[g])
    abs_v_eq = ABS(_v_n0, select_eq)
    abs_nt_eq = ABS(_new_t_n0, abs_v_eq)
    # abs_nt_eq : ... |- (\new_t v. @r. body[f]) = (\new_t v. @r. body[g])

    p.thus("_substitute_F f n = _substitute_F g n").by_unfold(
        abs_nt_eq, _SUBSTITUTE_F_DEF
    )


SUBSTITUTE_DEF, _SUBSTITUTE_REC_RAW = define_wf_lt(
    "substitute",
    _pred3_ty,
    _SUBSTITUTE_F,
    SUBSTITUTE_MONO,
)
SUBSTITUTE_REC = _unfold_rec_via_F_def(_SUBSTITUTE_REC_RAW, _SUBSTITUTE_F_DEF)


# Constructor recursion equations.
#
# Six cases reduce to a single ``r = K`` shape and use
# ``derive_rec_eq_select``. The two conditional cases (Var_t and
# Forall_f) collapse to ``(cond /\ r = T) \/ (~cond /\ r = E)`` and
# use ``derive_rec_eq_select_cond`` to produce a pair of conditional
# rec equations (``cond ==> rhs = T`` and ``~cond ==> rhs = E``).
SUBSTITUTE_AT_EMPTY = derive_rec_eq_select(
    SUBSTITUTE_REC,
    "Empty_t",
    [],
    [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_EQ = derive_rec_eq_select(
    SUBSTITUTE_REC,
    "Eq_f",
    ["t1", "t2"],
    [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_NOT = derive_rec_eq_select(
    SUBSTITUTE_REC,
    "Not_f",
    ["phi"],
    [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_IMP = derive_rec_eq_select(
    SUBSTITUTE_REC,
    "Imp_f",
    ["phi1", "phi2"],
    [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_INSERT = derive_rec_eq_select(
    SUBSTITUTE_REC,
    "Insert_t",
    ["t1", "t2"],
    [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_IN = derive_rec_eq_select(
    SUBSTITUTE_REC,
    "In_a",
    ["t1", "t2"],
    [_new_t_n0, _v_n0],
)
# Conditional cases: each yields a HIT (cond branch) and MISS (~cond
# branch) recursion equation.
SUBSTITUTE_AT_VAR_HIT, SUBSTITUTE_AT_VAR_MISS = derive_rec_eq_select_cond(
    SUBSTITUTE_REC,
    "Var_t",
    ["x"],
    [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_FORALL_HIT, SUBSTITUTE_AT_FORALL_MISS = derive_rec_eq_select_cond(
    SUBSTITUTE_REC,
    "Forall_f",
    ["a", "b"],
    [_new_t_n0, _v_n0],
)


# ---------------------------------------------------------------------------
# Stage 1 (d) -- substitute / is_term + is_form preservation.
#
# Used by Prov_HF-internal logic (PROV_HF_EXISTS_INTRO and downstream
# representability proofs) to discharge the ``is_form (substitute phi t
# v)`` side condition of CONTRAP / similar. The IS_TERM half is split
# off as a free-standing lemma because the IS_FORM cases for Eq_f / In_a
# (whose children are encoded HF terms, not formulas) need is_term
# preservation on each subterm -- the form-only IH cannot supply it.
#
# Both proofs are strong-induction on the encoded nat0; case-split via
# IS_TERM_REC / IS_FORM_REC's disjunctive characterisation; each
# constructor case rewrites through the matching SUBSTITUTE_AT_* equation
# and lifts via the IS_*_AT_* iff. Forall_f and Var_t use EXCLUDED_MIDDLE
# on ``v = bound`` to pick the HIT vs. MISS branch. Relocated from
# godel_first.py so hf_logic.py can consume it without a circular
# import.
# ---------------------------------------------------------------------------


@proof
def SUBSTITUTE_PRESERVES_IS_TERM(p):
    """|- !s t v. is_term s /\\ is_term t ==> is_term (substitute s t v).

    Substitution into a well-formed HF-term (replacing a variable index
    by a well-formed HF-term) yields a well-formed HF-term. Strong
    induction on ``s`` using SUBSTITUTE_AT_* / IS_TERM_AT_* on the
    Empty_t / Var_t / Insert_t cases.
    """
    p.goal(
        "!s. !t v. is_term s /\\ is_term t ==> is_term (substitute s t v)",
        types={"s": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    with p.strong_induction("s", "IH"):
        p.fix("t v")
        p.assume("(h_s, h_t): is_term s /\\ is_term t")

        # Disjunctive characterisation of is_term s.
        rec_at_s = SPEC(p._parse("s"), IS_TERM_REC)
        p.have(
            "h_disj: s = Empty_t \\/ (?x. s = Var_t x) "
            "\\/ (?a b. s = Insert_t a b /\\ is_term a /\\ is_term b)"
        ).by_eq_mp(rec_at_s, "h_s")

        # is_term Empty_t -- DISJ1 of REFL(Empty_t) into the IS_TERM_REC
        # body; needed by the Empty_t case below. Inline because hf_syntax
        # is upstream of the global ``IS_TERM_EMPTY`` lemma in hf_repr_core.
        rec_at_empty = SPEC(Empty_t, IS_TERM_REC)
        _empty_rhs = rand(rec_at_empty._concl)
        _empty_rest = rand(_empty_rhs)
        IS_TERM_EMPTY_TH = EQ_MP(
            SYM(rec_at_empty), DISJ1(REFL(Empty_t), _empty_rest)
        )

        is_term_const = mk_const("is_term", [])

        with p.cases_on("h_disj"):
            # --- Empty_t ---
            with p.case("c_empty: s = Empty_t"):
                p.have("h_subst: substitute s t v = Empty_t").by_rewrite(
                    ["c_empty", SUBSTITUTE_AT_EMPTY]
                )
                # DSL friction: ``by_rewrite_of(IS_TERM_EMPTY_TH,
                # [SYM(h_subst)])`` non-terminates -- the rewriter retries
                # the symmetric ``Empty_t = substitute s t v`` rule against
                # the running source until it exceeds the fixpoint cap. Use
                # AP_TERM + EQ_MP directly to avoid the rewrite loop.
                ap_eq = AP_TERM(is_term_const, p.fact("h_subst"))
                p.thus("is_term (substitute s t v)").by_eq_mp(
                    ap_eq, IS_TERM_EMPTY_TH
                )

            # --- Var_t x (HIT / MISS via EXCLUDED_MIDDLE on v = x) ---
            with p.case("c_var: ?x. s = Var_t x"):
                # auto-chooses x; x_eq: s = Var_t x.
                with p.cases_on(EXCLUDED_MIDDLE, "v = x"):
                    with p.case("hit: v = x"):
                        p.have(
                            "h_subst_inner: substitute (Var_t x) t v = t"
                        ).by(SUBSTITUTE_AT_VAR_HIT, "x", "t", "v", "hit")
                        p.have("h_subst: substitute s t v = t").by_rewrite_of(
                            "h_subst_inner", [SYM(p.fact("x_eq"))]
                        )
                        # DSL friction: ``by_rewrite_of("h_t",
                        # [SYM(h_subst)])`` non-terminates because the
                        # rule ``t = substitute s t v`` rewrites the ``t``
                        # inside the new RHS recursively. Use AP_TERM +
                        # EQ_MP for the clean lift.
                        ap_eq = AP_TERM(is_term_const, p.fact("h_subst"))
                        p.thus("is_term (substitute s t v)").by_eq_mp(
                            ap_eq, "h_t"
                        )
                    with p.case("miss: ~(v = x)"):
                        p.have(
                            "h_subst_inner: substitute (Var_t x) t v = Var_t x"
                        ).by(SUBSTITUTE_AT_VAR_MISS, "x", "t", "v", "miss")
                        p.have("h_subst: substitute s t v = s").by_rewrite_of(
                            "h_subst_inner", [SYM(p.fact("x_eq"))]
                        )
                        ap_eq = AP_TERM(is_term_const, p.fact("h_subst"))
                        p.thus("is_term (substitute s t v)").by_eq_mp(
                            ap_eq, "h_s"
                        )

            # --- Insert_t a b (recursive on both children) ---
            with p.case(
                "c_ins: ?a b. s = Insert_t a b /\\ is_term a /\\ is_term b"
            ):
                # auto-chooses a; a_eq: ?b. s = Insert_t a b /\ is_term a /\ is_term b.
                p.split("b_eq", "(s_eq, h_a, h_b)")
                p.have("lt_a: nat0_lt a s").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_INSERT_T_L),
                    ["s_eq"],
                )
                p.have("lt_b: nat0_lt b s").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_INSERT_T_R),
                    ["s_eq"],
                )
                p.have("hsub_a: is_term (substitute a t v)").by(
                    "IH", "a", "lt_a", "t", "v",
                    CONJ(p.fact("h_a"), p.fact("h_t")),
                )
                p.have("hsub_b: is_term (substitute b t v)").by(
                    "IH", "b", "lt_b", "t", "v",
                    CONJ(p.fact("h_b"), p.fact("h_t")),
                )
                p.have(
                    "h_subst: substitute s t v "
                    "= Insert_t (substitute a t v) (substitute b t v)"
                ).by_rewrite(["s_eq", SUBSTITUTE_AT_INSERT])
                at_ins = SPECL(
                    [p._parse("substitute a t v"), p._parse("substitute b t v")],
                    IS_TERM_AT_INSERT,
                )
                p.have(
                    "h_ins_term: is_term "
                    "(Insert_t (substitute a t v) (substitute b t v))"
                ).by_eq_mp(SYM(at_ins), CONJ(p.fact("hsub_a"), p.fact("hsub_b")))
                p.thus("is_term (substitute s t v)").by_rewrite_of(
                    "h_ins_term", [SYM(p.fact("h_subst"))]
                )


@proof
def SUBSTITUTE_PRESERVES_IS_FORM(p):
    """|- !phi t v. is_form phi /\\ is_term t ==> is_form (substitute phi t v).

    Strong induction on the formula encoding ``phi`` using IS_FORM_REC's
    case-split (Eq_f / Not_f / Imp_f / Forall_f / In_a). Atomic
    formula cases (Eq_f, In_a) delegate to SUBSTITUTE_PRESERVES_IS_TERM
    on each subterm; compound cases (Not_f, Imp_f, Forall_f) use the IH
    on subforms. Forall_f branches via EXCLUDED_MIDDLE on ``v = a`` to
    pick HIT (substitution stops, formula unchanged) vs. MISS (recurse
    on the body).

    Goal binder is named ``phi`` (not ``F``) because the parser resolves
    bare ``F`` to the boolean false constant; the published theorem is
    alpha-equivalent regardless of internal naming.
    """
    p.goal(
        "!phi. !t v. is_form phi /\\ is_term t ==> is_form (substitute phi t v)",
        types={"phi": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    is_form_const = mk_const("is_form", [])

    with p.strong_induction("phi", "IH"):
        p.fix("t v")
        p.assume("(h_phi, h_t): is_form phi /\\ is_term t")

        rec_at_phi = SPEC(p._parse("phi"), IS_FORM_REC)
        p.have(
            "h_disj: (?a b. phi = Eq_f a b /\\ is_term a /\\ is_term b) "
            "\\/ (?x. phi = Not_f x /\\ is_form x) "
            "\\/ (?a b. phi = Imp_f a b /\\ is_form a /\\ is_form b) "
            "\\/ (?a b. phi = Forall_f a b /\\ is_form b) "
            "\\/ (?a b. phi = In_a a b /\\ is_term a /\\ is_term b)"
        ).by_eq_mp(rec_at_phi, "h_phi")

        with p.cases_on("h_disj"):
            # --- Eq_f a b (atomic; both children are terms) ---
            with p.case(
                "c_eq: ?a b. phi = Eq_f a b /\\ is_term a /\\ is_term b"
            ):
                p.split("b_eq", "(phi_eq, h_a, h_b)")
                p.have("hsub_a: is_term (substitute a t v)").by(
                    SUBSTITUTE_PRESERVES_IS_TERM, "a", "t", "v",
                    CONJ(p.fact("h_a"), p.fact("h_t")),
                )
                p.have("hsub_b: is_term (substitute b t v)").by(
                    SUBSTITUTE_PRESERVES_IS_TERM, "b", "t", "v",
                    CONJ(p.fact("h_b"), p.fact("h_t")),
                )
                p.have(
                    "h_subst: substitute phi t v "
                    "= Eq_f (substitute a t v) (substitute b t v)"
                ).by_rewrite(["phi_eq", SUBSTITUTE_AT_EQ])
                at_eq = SPECL(
                    [p._parse("substitute a t v"), p._parse("substitute b t v")],
                    IS_FORM_AT_EQ,
                )
                p.have(
                    "h_eq_form: is_form "
                    "(Eq_f (substitute a t v) (substitute b t v))"
                ).by_eq_mp(SYM(at_eq), CONJ(p.fact("hsub_a"), p.fact("hsub_b")))
                p.thus("is_form (substitute phi t v)").by_rewrite_of(
                    "h_eq_form", [SYM(p.fact("h_subst"))]
                )

            # --- Not_f x (unary; recurse on body) ---
            with p.case("c_not: ?x. phi = Not_f x /\\ is_form x"):
                p.split("x_eq", "(phi_eq, h_x)")
                p.have("lt_x: nat0_lt x phi").by_rewrite_of(
                    SPEC(p._parse("x"), NAT0_LT_NOT_F), ["phi_eq"]
                )
                p.have("hsub_x: is_form (substitute x t v)").by(
                    "IH", "x", "lt_x", "t", "v",
                    CONJ(p.fact("h_x"), p.fact("h_t")),
                )
                p.have(
                    "h_subst: substitute phi t v = Not_f (substitute x t v)"
                ).by_rewrite(["phi_eq", SUBSTITUTE_AT_NOT])
                at_not = SPEC(p._parse("substitute x t v"), IS_FORM_AT_NOT)
                p.have(
                    "h_not_form: is_form (Not_f (substitute x t v))"
                ).by_eq_mp(SYM(at_not), "hsub_x")
                p.thus("is_form (substitute phi t v)").by_rewrite_of(
                    "h_not_form", [SYM(p.fact("h_subst"))]
                )

            # --- Imp_f a b (binary; recurse on both children) ---
            with p.case(
                "c_imp: ?a b. phi = Imp_f a b /\\ is_form a /\\ is_form b"
            ):
                p.split("b_eq", "(phi_eq, h_a, h_b)")
                p.have("lt_a: nat0_lt a phi").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_IMP_F_L),
                    ["phi_eq"],
                )
                p.have("lt_b: nat0_lt b phi").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_IMP_F_R),
                    ["phi_eq"],
                )
                p.have("hsub_a: is_form (substitute a t v)").by(
                    "IH", "a", "lt_a", "t", "v",
                    CONJ(p.fact("h_a"), p.fact("h_t")),
                )
                p.have("hsub_b: is_form (substitute b t v)").by(
                    "IH", "b", "lt_b", "t", "v",
                    CONJ(p.fact("h_b"), p.fact("h_t")),
                )
                p.have(
                    "h_subst: substitute phi t v "
                    "= Imp_f (substitute a t v) (substitute b t v)"
                ).by_rewrite(["phi_eq", SUBSTITUTE_AT_IMP])
                at_imp = SPECL(
                    [p._parse("substitute a t v"), p._parse("substitute b t v")],
                    IS_FORM_AT_IMP,
                )
                p.have(
                    "h_imp_form: is_form "
                    "(Imp_f (substitute a t v) (substitute b t v))"
                ).by_eq_mp(SYM(at_imp), CONJ(p.fact("hsub_a"), p.fact("hsub_b")))
                p.thus("is_form (substitute phi t v)").by_rewrite_of(
                    "h_imp_form", [SYM(p.fact("h_subst"))]
                )

            # --- Forall_f a b (HIT v=a leaves phi alone; MISS recurses) ---
            with p.case("c_fa: ?a b. phi = Forall_f a b /\\ is_form b"):
                p.split("b_eq", "(phi_eq, h_b)")
                with p.cases_on(EXCLUDED_MIDDLE, "v = a"):
                    with p.case("hit: v = a"):
                        p.have(
                            "h_subst_inner: substitute (Forall_f a b) t v "
                            "= Forall_f a b"
                        ).by(
                            SUBSTITUTE_AT_FORALL_HIT, "a", "b", "t", "v", "hit"
                        )
                        p.have(
                            "h_subst: substitute phi t v = phi"
                        ).by_rewrite_of(
                            "h_subst_inner", [SYM(p.fact("phi_eq"))]
                        )
                        # DSL friction: same non-termination as the Var_t
                        # HIT case in IS_TERM -- the rule ``phi = substitute
                        # phi t v`` rewrites the new RHS forever. Use
                        # AP_TERM + EQ_MP for the lift.
                        ap_eq = AP_TERM(is_form_const, p.fact("h_subst"))
                        p.thus("is_form (substitute phi t v)").by_eq_mp(
                            ap_eq, "h_phi"
                        )
                    with p.case("miss: ~(v = a)"):
                        p.have(
                            "h_subst_inner: substitute (Forall_f a b) t v "
                            "= Forall_f a (substitute b t v)"
                        ).by(
                            SUBSTITUTE_AT_FORALL_MISS,
                            "a", "b", "t", "v", "miss",
                        )
                        p.have(
                            "h_subst: substitute phi t v "
                            "= Forall_f a (substitute b t v)"
                        ).by_rewrite_of(
                            "h_subst_inner", [SYM(p.fact("phi_eq"))]
                        )
                        p.have("lt_b: nat0_lt b phi").by_rewrite_of(
                            SPECL(
                                [p._parse("a"), p._parse("b")],
                                NAT0_LT_FORALL_F_R,
                            ),
                            ["phi_eq"],
                        )
                        p.have("hsub_b: is_form (substitute b t v)").by(
                            "IH", "b", "lt_b", "t", "v",
                            CONJ(p.fact("h_b"), p.fact("h_t")),
                        )
                        at_fa = SPECL(
                            [p._parse("a"), p._parse("substitute b t v")],
                            IS_FORM_AT_FORALL,
                        )
                        p.have(
                            "h_fa_form: is_form "
                            "(Forall_f a (substitute b t v))"
                        ).by_eq_mp(SYM(at_fa), "hsub_b")
                        p.thus("is_form (substitute phi t v)").by_rewrite_of(
                            "h_fa_form", [SYM(p.fact("h_subst"))]
                        )

            # --- In_a a b (atomic; both children are terms) ---
            with p.case(
                "c_in: ?a b. phi = In_a a b /\\ is_term a /\\ is_term b"
            ):
                p.split("b_eq", "(phi_eq, h_a, h_b)")
                p.have("hsub_a: is_term (substitute a t v)").by(
                    SUBSTITUTE_PRESERVES_IS_TERM, "a", "t", "v",
                    CONJ(p.fact("h_a"), p.fact("h_t")),
                )
                p.have("hsub_b: is_term (substitute b t v)").by(
                    SUBSTITUTE_PRESERVES_IS_TERM, "b", "t", "v",
                    CONJ(p.fact("h_b"), p.fact("h_t")),
                )
                p.have(
                    "h_subst: substitute phi t v "
                    "= In_a (substitute a t v) (substitute b t v)"
                ).by_rewrite(["phi_eq", SUBSTITUTE_AT_IN])
                at_in = SPECL(
                    [p._parse("substitute a t v"), p._parse("substitute b t v")],
                    IS_FORM_AT_IN,
                )
                p.have(
                    "h_in_form: is_form "
                    "(In_a (substitute a t v) (substitute b t v))"
                ).by_eq_mp(SYM(at_in), CONJ(p.fact("hsub_a"), p.fact("hsub_b")))
                p.thus("is_form (substitute phi t v)").by_rewrite_of(
                    "h_in_form", [SYM(p.fact("h_subst"))]
                )


# ---------------------------------------------------------------------------
# Stage 1 (e) -- identity substitution.
#
#   |- !s v. is_term s ==> substitute s (Var_t v) v = s.
#   |- !phi v. is_form phi ==> substitute phi (Var_t v) v = phi.
#
# Substituting variable ``v`` with its own encoding ``Var_t v`` is the
# identity on well-formed terms / formulas. Substrate for the
# FORALL-IMPLICATION-DISTRIBUTION lemma (which feeds PROV_HF_EXISTS_ELIM
# in hf_logic.py): UI at the term ``Var_t v`` collapses
# ``substitute (F -> G) (Var_t v) v`` to ``F -> G`` so the
# DT-transformed Hilbert chain can use it under the assumption
# ``!v.(F -> G)``.
#
# Strong induction mirroring SUBSTITUTE_PRESERVES_IS_TERM /
# IS_FORM. Each calc chain rewrites the encoded constructor, applies
# the matching SUBSTITUTE_AT_*, lifts via AP_TERM / by_cong on
# constructor congruence, and folds back through SYM of the
# constructor-equation fact.
# ---------------------------------------------------------------------------


@proof
def IDENTITY_SUBSTITUTE_TERM(p):
    """|- !s v. is_term s ==> substitute s (Var_t v) v = s.

    Strong induction on ``s``; case-split via IS_TERM_REC. Var_t HIT
    (v = x) collapses to ``Var_t v = Var_t x = s`` via AP_TERM
    congruence on ``Var_t``; Var_t MISS (~(v = x)) leaves
    ``substitute (Var_t x) (Var_t v) v = Var_t x`` directly. Insert_t
    chains the IH on each child.
    """
    p.goal(
        "!s. !v. is_term s ==> substitute s (Var_t v) v = s",
        types={"s": nat0_ty, "v": nat0_ty},
    )
    with p.strong_induction("s", "IH"):
        p.fix("v")
        p.assume("h_s: is_term s")
        rec_at_s = SPEC(p._parse("s"), IS_TERM_REC)
        p.have(
            "h_disj: s = Empty_t \\/ (?x. s = Var_t x) "
            "\\/ (?a b. s = Insert_t a b /\\ is_term a /\\ is_term b)"
        ).by_eq_mp(rec_at_s, "h_s")

        with p.cases_on("h_disj"):
            # --- Empty_t ---
            with p.case("c_empty: s = Empty_t"):
                with p.calc("substitute s (Var_t v) v", thus=True) as c:
                    c.step("= substitute Empty_t (Var_t v) v").by_rewrite(
                        ["c_empty"]
                    )
                    c.step("= Empty_t").by(
                        SUBSTITUTE_AT_EMPTY, "Var_t v", "v"
                    )
                    c.step("= s").by_thm(SYM(p.fact("c_empty")))

            # --- Var_t x ---
            with p.case("c_var: ?x. s = Var_t x"):
                with p.cases_on(EXCLUDED_MIDDLE, "v = x"):
                    with p.case("hit: v = x"):
                        with p.calc(
                            "substitute s (Var_t v) v", thus=True
                        ) as c:
                            c.step("= substitute (Var_t x) (Var_t v) v").by_rewrite(
                                ["x_eq"]
                            )
                            c.step("= Var_t v").by(
                                SUBSTITUTE_AT_VAR_HIT,
                                "x", "Var_t v", "v", "hit",
                            )
                            # Var_t v = Var_t x via AP_TERM(Var_t, hit).
                            c.step("= Var_t x").by_cong("Var_t", "hit")
                            c.step("= s").by_thm(SYM(p.fact("x_eq")))
                    with p.case("miss: ~(v = x)"):
                        with p.calc(
                            "substitute s (Var_t v) v", thus=True
                        ) as c:
                            c.step("= substitute (Var_t x) (Var_t v) v").by_rewrite(
                                ["x_eq"]
                            )
                            c.step("= Var_t x").by(
                                SUBSTITUTE_AT_VAR_MISS,
                                "x", "Var_t v", "v", "miss",
                            )
                            c.step("= s").by_thm(SYM(p.fact("x_eq")))

            # --- Insert_t a b ---
            with p.case(
                "c_ins: ?a b. s = Insert_t a b /\\ is_term a /\\ is_term b"
            ):
                p.split("b_eq", "(s_eq, h_a, h_b)")
                p.have("lt_a: nat0_lt a s").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_INSERT_T_L),
                    ["s_eq"],
                )
                p.have("lt_b: nat0_lt b s").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_INSERT_T_R),
                    ["s_eq"],
                )
                p.have("ih_a: substitute a (Var_t v) v = a").by(
                    "IH", "a", "lt_a", "v", "h_a",
                )
                p.have("ih_b: substitute b (Var_t v) v = b").by(
                    "IH", "b", "lt_b", "v", "h_b",
                )
                with p.calc("substitute s (Var_t v) v", thus=True) as c:
                    c.step("= substitute (Insert_t a b) (Var_t v) v").by_rewrite(
                        ["s_eq"]
                    )
                    c.step(
                        "= Insert_t (substitute a (Var_t v) v) "
                        "(substitute b (Var_t v) v)"
                    ).by(SUBSTITUTE_AT_INSERT, "a", "b", "Var_t v", "v")
                    c.step("= Insert_t a b").by_cong("Insert_t", "ih_a", "ih_b")
                    c.step("= s").by_thm(SYM(p.fact("s_eq")))


@proof
def IDENTITY_SUBSTITUTE(p):
    """|- !phi v. is_form phi ==> substitute phi (Var_t v) v = phi.

    Strong induction on ``phi`` via IS_FORM_REC. Atomic-formula cases
    (Eq_f, In_a) delegate to IDENTITY_SUBSTITUTE_TERM on each
    subterm; compound cases (Not_f, Imp_f, Forall_f-MISS) chain the
    IH on subforms; Forall_f-HIT (v = a) is immediate since
    ``substitute (Forall_f a b) (Var_t v) v = Forall_f a b`` already.
    """
    p.goal(
        "!phi. !v. is_form phi ==> substitute phi (Var_t v) v = phi",
        types={"phi": nat0_ty, "v": nat0_ty},
    )
    with p.strong_induction("phi", "IH"):
        p.fix("v")
        p.assume("h_phi: is_form phi")
        rec_at_phi = SPEC(p._parse("phi"), IS_FORM_REC)
        p.have(
            "h_disj: (?a b. phi = Eq_f a b /\\ is_term a /\\ is_term b) "
            "\\/ (?x. phi = Not_f x /\\ is_form x) "
            "\\/ (?a b. phi = Imp_f a b /\\ is_form a /\\ is_form b) "
            "\\/ (?a b. phi = Forall_f a b /\\ is_form b) "
            "\\/ (?a b. phi = In_a a b /\\ is_term a /\\ is_term b)"
        ).by_eq_mp(rec_at_phi, "h_phi")

        with p.cases_on("h_disj"):
            # --- Eq_f a b ---
            with p.case(
                "c_eq: ?a b. phi = Eq_f a b /\\ is_term a /\\ is_term b"
            ):
                p.split("b_eq", "(phi_eq, h_a, h_b)")
                p.have("ih_a: substitute a (Var_t v) v = a").by(
                    IDENTITY_SUBSTITUTE_TERM, "a", "v", "h_a",
                )
                p.have("ih_b: substitute b (Var_t v) v = b").by(
                    IDENTITY_SUBSTITUTE_TERM, "b", "v", "h_b",
                )
                with p.calc("substitute phi (Var_t v) v", thus=True) as c:
                    c.step("= substitute (Eq_f a b) (Var_t v) v").by_rewrite(
                        ["phi_eq"]
                    )
                    c.step(
                        "= Eq_f (substitute a (Var_t v) v) "
                        "(substitute b (Var_t v) v)"
                    ).by(SUBSTITUTE_AT_EQ, "a", "b", "Var_t v", "v")
                    c.step("= Eq_f a b").by_cong("Eq_f", "ih_a", "ih_b")
                    c.step("= phi").by_thm(SYM(p.fact("phi_eq")))

            # --- Not_f x ---
            with p.case("c_not: ?x. phi = Not_f x /\\ is_form x"):
                p.split("x_eq", "(phi_eq, h_x)")
                p.have("lt_x: nat0_lt x phi").by_rewrite_of(
                    SPEC(p._parse("x"), NAT0_LT_NOT_F), ["phi_eq"]
                )
                p.have("ih_x: substitute x (Var_t v) v = x").by(
                    "IH", "x", "lt_x", "v", "h_x",
                )
                with p.calc("substitute phi (Var_t v) v", thus=True) as c:
                    c.step("= substitute (Not_f x) (Var_t v) v").by_rewrite(
                        ["phi_eq"]
                    )
                    c.step("= Not_f (substitute x (Var_t v) v)").by(
                        SUBSTITUTE_AT_NOT, "x", "Var_t v", "v"
                    )
                    c.step("= Not_f x").by_cong("Not_f", "ih_x")
                    c.step("= phi").by_thm(SYM(p.fact("phi_eq")))

            # --- Imp_f a b ---
            with p.case(
                "c_imp: ?a b. phi = Imp_f a b /\\ is_form a /\\ is_form b"
            ):
                p.split("b_eq", "(phi_eq, h_a, h_b)")
                p.have("lt_a: nat0_lt a phi").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_IMP_F_L),
                    ["phi_eq"],
                )
                p.have("lt_b: nat0_lt b phi").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_IMP_F_R),
                    ["phi_eq"],
                )
                p.have("ih_a: substitute a (Var_t v) v = a").by(
                    "IH", "a", "lt_a", "v", "h_a",
                )
                p.have("ih_b: substitute b (Var_t v) v = b").by(
                    "IH", "b", "lt_b", "v", "h_b",
                )
                with p.calc("substitute phi (Var_t v) v", thus=True) as c:
                    c.step("= substitute (Imp_f a b) (Var_t v) v").by_rewrite(
                        ["phi_eq"]
                    )
                    c.step(
                        "= Imp_f (substitute a (Var_t v) v) "
                        "(substitute b (Var_t v) v)"
                    ).by(SUBSTITUTE_AT_IMP, "a", "b", "Var_t v", "v")
                    c.step("= Imp_f a b").by_cong("Imp_f", "ih_a", "ih_b")
                    c.step("= phi").by_thm(SYM(p.fact("phi_eq")))

            # --- Forall_f a b (HIT v=a is trivial; MISS recurses on b) ---
            with p.case("c_fa: ?a b. phi = Forall_f a b /\\ is_form b"):
                p.split("b_eq", "(phi_eq, h_b)")
                with p.cases_on(EXCLUDED_MIDDLE, "v = a"):
                    with p.case("hit: v = a"):
                        with p.calc(
                            "substitute phi (Var_t v) v", thus=True
                        ) as c:
                            c.step("= substitute (Forall_f a b) (Var_t v) v").by_rewrite(
                                ["phi_eq"]
                            )
                            c.step("= Forall_f a b").by(
                                SUBSTITUTE_AT_FORALL_HIT,
                                "a", "b", "Var_t v", "v", "hit",
                            )
                            c.step("= phi").by_thm(SYM(p.fact("phi_eq")))
                    with p.case("miss: ~(v = a)"):
                        p.have("lt_b: nat0_lt b phi").by_rewrite_of(
                            SPECL(
                                [p._parse("a"), p._parse("b")],
                                NAT0_LT_FORALL_F_R,
                            ),
                            ["phi_eq"],
                        )
                        p.have("ih_b: substitute b (Var_t v) v = b").by(
                            "IH", "b", "lt_b", "v", "h_b",
                        )
                        with p.calc(
                            "substitute phi (Var_t v) v", thus=True
                        ) as c:
                            c.step("= substitute (Forall_f a b) (Var_t v) v").by_rewrite(
                                ["phi_eq"]
                            )
                            c.step(
                                "= Forall_f a (substitute b (Var_t v) v)"
                            ).by(
                                SUBSTITUTE_AT_FORALL_MISS,
                                "a", "b", "Var_t v", "v", "miss",
                            )
                            # Forall_f a (substitute b ...) = Forall_f a b
                            # via AP_TERM(Forall_f a, ih_b).
                            c.step("= Forall_f a b").by_cong(
                                p._parse("Forall_f a"), "ih_b"
                            )
                            c.step("= phi").by_thm(SYM(p.fact("phi_eq")))

            # --- In_a a b ---
            with p.case(
                "c_in: ?a b. phi = In_a a b /\\ is_term a /\\ is_term b"
            ):
                p.split("b_eq", "(phi_eq, h_a, h_b)")
                p.have("ih_a: substitute a (Var_t v) v = a").by(
                    IDENTITY_SUBSTITUTE_TERM, "a", "v", "h_a",
                )
                p.have("ih_b: substitute b (Var_t v) v = b").by(
                    IDENTITY_SUBSTITUTE_TERM, "b", "v", "h_b",
                )
                with p.calc("substitute phi (Var_t v) v", thus=True) as c:
                    c.step("= substitute (In_a a b) (Var_t v) v").by_rewrite(
                        ["phi_eq"]
                    )
                    c.step(
                        "= In_a (substitute a (Var_t v) v) "
                        "(substitute b (Var_t v) v)"
                    ).by(SUBSTITUTE_AT_IN, "a", "b", "Var_t v", "v")
                    c.step("= In_a a b").by_cong("In_a", "ih_a", "ih_b")
                    c.step("= phi").by_thm(SYM(p.fact("phi_eq")))


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 1 (a) -- term/form datatype.")
    print("  Term constructors:")
    print("    VAR_T_DEF     :", pp_thm(VAR_T_DEF))
    print("    VAR_T_AT      :", pp_thm(VAR_T_AT))
    print("  Form constructors:")
    print("    EQ_F_DEF      :", pp_thm(EQ_F_DEF))
    print("    EQ_F_AT       :", pp_thm(EQ_F_AT))
    print("    NOT_F_DEF     :", pp_thm(NOT_F_DEF))
    print("    NOT_F_AT      :", pp_thm(NOT_F_AT))
    print("    IMP_F_DEF     :", pp_thm(IMP_F_DEF))
    print("    IMP_F_AT      :", pp_thm(IMP_F_AT))
    print("    FORALL_F_DEF  :", pp_thm(FORALL_F_DEF))
    print("    FORALL_F_AT   :", pp_thm(FORALL_F_AT))
    print("  HF primitives:")
    print("    EMPTY_T_DEF   :", pp_thm(EMPTY_T_DEF))
    print("    INSERT_T_DEF  :", pp_thm(INSERT_T_DEF))
    print("    INSERT_T_AT   :", pp_thm(INSERT_T_AT))
    print("    IN_A_DEF      :", pp_thm(IN_A_DEF))
    print("    IN_A_AT       :", pp_thm(IN_A_AT))
    print()
    print("Stage 1 -- size lemmas (foundation for define_wf_lt MONO proofs).")
    print("  Unary constructors:")
    print("    NAT0_LT_VAR_T   :", pp_thm(NAT0_LT_VAR_T))
    print("    NAT0_LT_NOT_F   :", pp_thm(NAT0_LT_NOT_F))
    print("  Binary constructors (left / right slot):")
    print("    NAT0_LT_EQ_F_L    :", pp_thm(NAT0_LT_EQ_F_L))
    print("    NAT0_LT_EQ_F_R    :", pp_thm(NAT0_LT_EQ_F_R))
    print("    NAT0_LT_IMP_F_L   :", pp_thm(NAT0_LT_IMP_F_L))
    print("    NAT0_LT_IMP_F_R   :", pp_thm(NAT0_LT_IMP_F_R))
    print("    NAT0_LT_FORALL_F_L:", pp_thm(NAT0_LT_FORALL_F_L))
    print("    NAT0_LT_FORALL_F_R:", pp_thm(NAT0_LT_FORALL_F_R))
    print()
    print("Stage 1 -- constructor injectivity.")
    print("  Unary:")
    print("    VAR_T_INJ     :", pp_thm(VAR_T_INJ))
    print("    NOT_F_INJ     :", pp_thm(NOT_F_INJ))
    print("  Binary:")
    print("    EQ_F_INJ      :", pp_thm(EQ_F_INJ))
    print("    IMP_F_INJ     :", pp_thm(IMP_F_INJ))
    print("    FORALL_F_INJ  :", pp_thm(FORALL_F_INJ))
    print()
    print("Stage 1 -- constructor disjointness.")
    print("  Each non-empty constructor C: !args. ~(C args = Empty_t):")
    print("    VAR_T_NEQ_EMPTY    :", pp_thm(VAR_T_NEQ_EMPTY))
    print("    NOT_F_NEQ_EMPTY    :", pp_thm(NOT_F_NEQ_EMPTY))
    print("    EQ_F_NEQ_EMPTY     :", pp_thm(EQ_F_NEQ_EMPTY))
    print("    IMP_F_NEQ_EMPTY    :", pp_thm(IMP_F_NEQ_EMPTY))
    print("    FORALL_F_NEQ_EMPTY :", pp_thm(FORALL_F_NEQ_EMPTY))
    print(
        f"  Pairwise distinct-tag disjointness: {len(CTOR_DISJOINTNESS)} lemmas, e.g."
    )
    print("    EQ_F_NEQ_FORALL_F :", pp_thm(CTOR_DISJOINTNESS[("Eq_f", "Forall_f")]))
    print()
    print("Stage 1 -- MONO helpers (per-disjunct iffs).")
    # Smoke test: build a fake hypothesis ASSUME(!k. nat0_lt k n ==> f k = g k)
    # and exercise both helpers against the hf_syntax constructors.
    from axioms import mk_forall, mk_imp
    from basics import mk_app as _mk_app

    _f_smoke = Var("f", parse_type("nat0 -> bool"))
    _g_smoke = Var("g", parse_type("nat0 -> bool"))
    _n_smoke = Var("n", nat0_ty)
    _k_smoke = Var("k", nat0_ty)
    _nat0_lt_const = mk_const("nat0_lt", [])
    _smoke_hyp = ASSUME(
        mk_forall(
            _k_smoke,
            mk_imp(
                _mk_app(_nat0_lt_const, _k_smoke, _n_smoke),
                mk_eq(_mk_app(_f_smoke, _k_smoke), _mk_app(_g_smoke, _k_smoke)),
            ),
        )
    )
    _IFF_NOT_F = mono_iff_unary_step(Not_f, NAT0_LT_NOT_F, _smoke_hyp)
    _IFF_INSERT_T = mono_iff_binary_step(
        Insert_t,
        NAT0_LT_INSERT_T_L,
        NAT0_LT_INSERT_T_R,
        _smoke_hyp,
    )
    print("  unary  (Not_f)    :", pp_thm(_IFF_NOT_F))
    print("  binary (Insert_t) :", pp_thm(_IFF_INSERT_T))
    print()
    print("Stage 1 -- derive_rec_eq smoke test (synthetic recursive body).")
    # Synthetic predicate F : nat0 -> bool with body matching is_term shape.
    _F_pred = Var("F", parse_type("nat0 -> bool"))
    _n_var = Var("n", nat0_ty)
    _v_smoke = Var("v", nat0_ty)
    _a_smoke = Var("a", nat0_ty)
    _b_smoke = Var("b", nat0_ty)
    _body = mk_or(
        mk_eq(_n_var, Empty_t),
        mk_or(
            mk_exists(_v_smoke, mk_eq(_n_var, _mk_app(Var_t, _v_smoke))),
            mk_exists(
                _a_smoke,
                mk_exists(
                    _b_smoke,
                    mk_and(
                        mk_eq(_n_var, _mk_app(Insert_t, _a_smoke, _b_smoke)),
                        mk_and(
                            _mk_app(_F_pred, _a_smoke), _mk_app(_F_pred, _b_smoke)
                        ),
                    ),
                ),
            ),
        ),
    )
    _fake_REC = ASSUME(mk_forall(_n_var, mk_eq(_mk_app(_F_pred, _n_var), _body)))
    _REC_VAR = derive_rec_eq(_fake_REC, "Var_t", ["v"])
    _REC_INSERT = derive_rec_eq(_fake_REC, "Insert_t", ["a", "b"])
    print("  REC at Var_t    :", pp_thm(_REC_VAR))
    print("  REC at Insert_t :", pp_thm(_REC_INSERT))
    print()
    print("Stage 1 (b) -- is_term predicate.")
    print("    _IS_TERM_F_DEF :", pp_thm(_IS_TERM_F_DEF))
    print("    IS_TERM_MONO   :", pp_thm(IS_TERM_MONO))
    print("    IS_TERM_DEF    :", pp_thm(IS_TERM_DEF))
    print("    IS_TERM_REC    :", pp_thm(IS_TERM_REC))
    print("    IS_TERM_AT_VAR   :", pp_thm(IS_TERM_AT_VAR))
    print("    IS_TERM_AT_INSERT:", pp_thm(IS_TERM_AT_INSERT))
    print()
    print("Stage 1 (b) -- is_form predicate.")
    print("    IS_FORM_MONO   :", pp_thm(IS_FORM_MONO))
    print("    IS_FORM_DEF    :", pp_thm(IS_FORM_DEF))
    print("    IS_FORM_REC    :", pp_thm(IS_FORM_REC))
    print("    IS_FORM_AT_EQ     :", pp_thm(IS_FORM_AT_EQ))
    print("    IS_FORM_AT_NOT    :", pp_thm(IS_FORM_AT_NOT))
    print("    IS_FORM_AT_IMP    :", pp_thm(IS_FORM_AT_IMP))
    print("    IS_FORM_AT_FORALL :", pp_thm(IS_FORM_AT_FORALL))
    print("    IS_FORM_AT_IN     :", pp_thm(IS_FORM_AT_IN))
    print()
    print("Stage 1 (c) -- free_in predicate.")
    print("    FREE_IN_MONO   :", pp_thm(FREE_IN_MONO))
    print("    FREE_IN_DEF    :", pp_thm(FREE_IN_DEF))
    print("    FREE_IN_REC    :", pp_thm(FREE_IN_REC))
    print("    FREE_IN_AT_VAR    :", pp_thm(FREE_IN_AT_VAR))
    print("    FREE_IN_AT_EQ     :", pp_thm(FREE_IN_AT_EQ))
    print("    FREE_IN_AT_NOT    :", pp_thm(FREE_IN_AT_NOT))
    print("    FREE_IN_AT_IMP    :", pp_thm(FREE_IN_AT_IMP))
    print("    FREE_IN_AT_FORALL :", pp_thm(FREE_IN_AT_FORALL))
    print("    FREE_IN_AT_INSERT :", pp_thm(FREE_IN_AT_INSERT))
    print("    FREE_IN_AT_IN     :", pp_thm(FREE_IN_AT_IN))
    print()
    print("Stage 1 (c) -- substitute.")
    print("    SUBSTITUTE_MONO         :", pp_thm(SUBSTITUTE_MONO))
    print("    SUBSTITUTE_DEF          :", pp_thm(SUBSTITUTE_DEF))
    print("    SUBSTITUTE_REC          :", pp_thm(SUBSTITUTE_REC))
    print("    SUBSTITUTE_AT_EMPTY     :", pp_thm(SUBSTITUTE_AT_EMPTY))
    print("    SUBSTITUTE_AT_VAR_HIT   :", pp_thm(SUBSTITUTE_AT_VAR_HIT))
    print("    SUBSTITUTE_AT_VAR_MISS  :", pp_thm(SUBSTITUTE_AT_VAR_MISS))
    print("    SUBSTITUTE_AT_EQ        :", pp_thm(SUBSTITUTE_AT_EQ))
    print("    SUBSTITUTE_AT_NOT       :", pp_thm(SUBSTITUTE_AT_NOT))
    print("    SUBSTITUTE_AT_IMP       :", pp_thm(SUBSTITUTE_AT_IMP))
    print("    SUBSTITUTE_AT_FORALL_HIT :", pp_thm(SUBSTITUTE_AT_FORALL_HIT))
    print("    SUBSTITUTE_AT_FORALL_MISS:", pp_thm(SUBSTITUTE_AT_FORALL_MISS))
    print("    SUBSTITUTE_AT_INSERT     :", pp_thm(SUBSTITUTE_AT_INSERT))
    print("    SUBSTITUTE_AT_IN         :", pp_thm(SUBSTITUTE_AT_IN))
    print()
    print("Stage 1 (d) -- substitute / is_term + is_form preservation.")
    print(
        "    SUBSTITUTE_PRESERVES_IS_TERM :",
        pp_thm(SUBSTITUTE_PRESERVES_IS_TERM),
    )
    print(
        "    SUBSTITUTE_PRESERVES_IS_FORM :",
        pp_thm(SUBSTITUTE_PRESERVES_IS_FORM),
    )
    print()
    print("Stage 1 (e) -- identity substitution.")
    print(
        "    IDENTITY_SUBSTITUTE_TERM :",
        pp_thm(IDENTITY_SUBSTITUTE_TERM),
    )
    print(
        "    IDENTITY_SUBSTITUTE      :",
        pp_thm(IDENTITY_SUBSTITUTE),
    )
