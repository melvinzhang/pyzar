# ---------------------------------------------------------------------------
# Stage 1 -- syntax of Q encoded as HF.
# ---------------------------------------------------------------------------
#
# Q's signature: 0, S, +, *, =, plus first-order connectives and
# quantifiers. We pick an inductive grammar:
#
#   Term  ::=  Zero | Succ Term | Var num | Plus Term Term | Times Term Term
#   Form  ::=  Eq Term Term | Not Form | Imp Form Form | Forall num Form
#
# (And, Or, Exists, Iff are sugar.) Each constructor has an arity; encode
# a node ``Constructor(arg1, ..., argk)`` as the HF set
#
#   { 0 |-> tag, 1 |-> arg1, ..., k |-> argk }
#
# i.e. an ordered tuple stored as the HF set of (index, value) pairs.
# Tags are small naturals: Zero = 0, Succ = 1, Var = 2, Plus = 3, etc.
#
# Goedel numbering is then literally ``rep_hf`` from ``hf_sets.py``.
# ``godelnum : term + form -> num`` is a one-line composition of the
# encoding above with ``rep_hf``.
#
# Standard lemmas (all by structural induction or by the unique-readability
# theorem for HF tuples):
#
#   |- !t1 t2. godelnum t1 = godelnum t2 ==> t1 = t2          (injectivity)
#   |- decidable: "is this num the godelnum of a well-formed term/form?"
#   |- substitute(x, t, F) is primitive recursive on godelnums

r"""Syntax of Robinson's Q encoded as nat0 (Stage 1 of ``godel_first.py``).

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

from fusion import Var, ASSUME, DEDUCT_ANTISYM_RULE, REFL, vsubst, INST_TYPE
from basics import mk_const, mk_app, mk_eq, mk_abs, dest_eq, is_eq, rator, rand
from parser import define, parse_type
from axioms import (
    F, mk_and, mk_exists, mk_not, mk_or, mk_select,
    dest_conj, dest_forall, dest_imp, dest_exists, dest_disj,
    SELECT_AX, aty,
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
from proof import proof
from fusion import ABS
from tactics import (
    SPEC, SPECL, GEN, GENL, SYM, EQ_MP, MP, CONJ, CONJUNCT1, CONJUNCT2,
    EXISTS, CHOOSE_WITNESS, REWRITE_RULE, REWRITE_CONV, EQF_INTRO, NOT_ELIM,
    DISCH, CONTR, TRANS, AP_TERM, AP_THM, BETA_CONV, BETA_NORM,
    DISJ1, DISJ2, DISJ_CASES,
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
        raise ValueError(
            f"_extract_nfg: hyp_th not !k. ...; got {hyp_th._concl}"
        )
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
    sl_at_w = SPEC(w_t, size_lemma)              # |- nat0_lt w (ctor w)
    lt_w_n = REWRITE_RULE([SYM(n_eq_l)], sl_at_w)  # {LHS} |- nat0_lt w n
    fw_eq_gw = MP(SPEC(w_t, hyp_th), lt_w_n)       # {LHS} |- f w = g w
    gw_th = EQ_MP(fw_eq_gw, fw_th)                 # {LHS} |- g w
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
        target_inner_pred_body = mk_abs(b_var, target_inner_body)
        target_outer_pred_body = mk_abs(
            a_var, mk_exists(b_var, target_inner_body)
        )
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
        target_outer_pred_body = mk_abs(
            a_var, mk_exists(b_var, target_inner_body)
        )
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


def _mono_iff_binary_pw_step(ctor, size_lemma_l, size_lemma_r,
                             hyp_th, v_term, rest_builder, recurses_l):
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
        target_outer_pred_body = mk_abs(
            a_var, mk_exists(b_var, target_inner_body)
        )
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


def mono_iff_binary_disj_pw_step(ctor, size_lemma_l, size_lemma_r,
                                 hyp_th, v_term):
    """``(?a b. n = ctor a b /\\ (f a v \\/ f b v))
        = (?a b. n = ctor a b /\\ (g a v \\/ g b v))``."""
    return _mono_iff_binary_pw_step(
        ctor, size_lemma_l, size_lemma_r, hyp_th, v_term,
        rest_builder=lambda fn, a, b, v: mk_or(
            mk_app(fn, a, v), mk_app(fn, b, v)
        ),
        recurses_l=True,
    )


def mono_iff_forall_pw_step(size_lemma_r, hyp_th, v_term):
    """``(?a b. n = Forall_f a b /\\ ~(v = a) /\\ f b v)
        = (?a b. n = Forall_f a b /\\ ~(v = a) /\\ g b v)``.

    The ``a`` slot is the bound-variable index of the encoded universal;
    only the body slot ``b`` recurses through ``f``."""
    return _mono_iff_binary_pw_step(
        Forall_f, None, size_lemma_r, hyp_th, v_term,
        rest_builder=lambda fn, a, b, v: mk_and(
            mk_not(mk_eq(v, a)), mk_app(fn, b, v)
        ),
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


def _mono_iff_value_binary_pw_step(ctor, size_lemma_l, size_lemma_r,
                                   hyp_th, args, rest_builder, recurses_l):
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
        return mk_and(mk_eq(n_t, ctor_ab),
                      rest_builder(fn, a_var, b_var, args))

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
        target_outer_pred_body = mk_abs(
            a_var, mk_exists(b_var, target_inner_body)
        )
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


def mono_iff_value_binary_pw_step(ctor, size_lemma_l, size_lemma_r,
                                  hyp_th, args, r_term, value_fn):
    """``(?a b. n = ctor a b /\\ r = value_fn(f a args, f b args))
        = (?a b. n = ctor a b /\\ r = value_fn(g a args, g b args))``.

    ``value_fn(a_term, b_term)`` builds the value -- typically
    ``lambda a, b: mk_app(ctor, a, b)``.
    """
    return _mono_iff_value_binary_pw_step(
        ctor, size_lemma_l, size_lemma_r, hyp_th, args,
        rest_builder=lambda fn, a, b, ags: mk_eq(
            r_term,
            value_fn(mk_app(fn, a, *ags), mk_app(fn, b, *ags)),
        ),
        recurses_l=True,
    )


def mono_iff_forall_value_pw_step(size_lemma_r, hyp_th, args, r_term,
                                  v_for_eq):
    """Per-disjunct iff for the ``Forall_f`` value disjunct.

    Body shape (LHS):
      ``?a b. n = Forall_f a b /\\
              ((v_for_eq = a /\\ r = Forall_f a b) \\/
               (~(v_for_eq = a) /\\ r = Forall_f a (f b args)))``.

    Only ``b`` recurses; the ``v_for_eq = a`` ``then`` branch has no
    f-reference.
    """
    return _mono_iff_value_binary_pw_step(
        Forall_f, None, size_lemma_r, hyp_th, args,
        rest_builder=lambda fn, a, b, ags: mk_or(
            mk_and(mk_eq(v_for_eq, a),
                   mk_eq(r_term, mk_app(Forall_f, a, b))),
            mk_and(mk_not(mk_eq(v_for_eq, a)),
                   mk_eq(r_term, mk_app(Forall_f, a,
                                        mk_app(fn, b, *ags)))),
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
    spec_p = SPEC(pred, sel_ax_at)              # |- !x. P x ==> P (@P)
    spec_x = SPEC(K_t, spec_p)                  # |- P K ==> P (@P)
    p_at_K = mk_app(pred, K_t)
    bridge_K = BETA_CONV(p_at_K)                # |- P K = (K = K)
    p_K_th = EQ_MP(SYM(bridge_K), REFL(K_t))    # |- P K
    p_at_select = MP(spec_x, p_K_th)            # |- P (@P)
    sel_t = mk_select(r_var, mk_eq(r_var, K_t))
    bridge_sel = BETA_CONV(mk_app(pred, sel_t)) # |- P (@P) = ((@P) = K)
    return EQ_MP(bridge_sel, p_at_select)       # |- (@r. r = K) = K


# ---------------------------------------------------------------------------
# Constructor recursion-equation derivation.
#
# Given a recursive predicate F : nat0 -> bool defined via define_wf_lt
# with REC of shape ``|- !n. F n = body[F, n]``, where each body disjunct
# has one of the q-syntax shapes:
#
#   (n = K)                                  -- nullary base (e.g. Zero_t)
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


# Lookup tables: NEQ_ZERO and INJ lemmas indexed by constructor name.
_CTOR_NEQ_ZERO = {
    "Succ_t": SUCC_T_NEQ_ZERO, "Var_t": VAR_T_NEQ_ZERO,
    "Plus_t": PLUS_T_NEQ_ZERO, "Times_t": TIMES_T_NEQ_ZERO,
    "Eq_f": EQ_F_NEQ_ZERO, "Not_f": NOT_F_NEQ_ZERO,
    "Imp_f": IMP_F_NEQ_ZERO, "Forall_f": FORALL_F_NEQ_ZERO,
}
_CTOR_INJ = {
    "Succ_t": SUCC_T_INJ, "Var_t": VAR_T_INJ, "Not_f": NOT_F_INJ,
    "Plus_t": PLUS_T_INJ, "Times_t": TIMES_T_INJ,
    "Eq_f": EQ_F_INJ, "Imp_f": IMP_F_INJ, "Forall_f": FORALL_F_INJ,
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
      - ``n = Zero_t`` -> "Zero_t"
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
        raise ValueError(
            f"_disjunct_ctor_name: cannot pin down constructor in {disj}"
        )
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
    F_th = MP(NOT_ELIM(neq_specd), head_eq_th)   # {disj} |- F
    rev = CONTR(disj, ASSUME(F))                  # {F} |- disj
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
    head_th = CONJUNCT1(chosen)   # {disj} |- target_app = C x
    rest_th = CONJUNCT2(chosen)   # {disj} |- R(x)
    # SYM head_th: |- C x = target_app. But target_app = C target_arg.
    # Use inj_lemma: C target_arg = C x ==> target_arg = x. From head_th
    # rewritten: C target_arg = C x. So target_arg = x.
    # Determine the witness term used by CHOOSE.
    sel_x = rand(head_th._concl)  # = C x
    x_val = rand(sel_x)           # = x (the SELECT term)
    inj_at = SPECL([target_arg, x_val], inj_lemma)  # |- C target_arg = C x ==> target_arg = x
    # head_th : {disj} |- target_app = C x. We have target_app = C target_arg by REFL of target_app.
    # Actually target_app is literally `C target_arg` (same term), so no rewrite needed.
    targ_eq_x = MP(inj_at, head_th)   # {disj} |- target_arg = x
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
    pair = MP(inj_at, head_th)              # {disj} |- a_t = wa /\ b_t = wb
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


def _ctor_neq_lemma(ctor_a_name, ctor_b_name):
    """Look up ``|- !args1 args2. ~(ctor_a args1 = ctor_b args2)`` from
    the precomputed registry (``CTOR_DISJOINTNESS`` + ``_NEQ_ZERO`` family)."""
    if ctor_a_name == "Zero_t":
        # ~(Zero_t = ctor_b args). Symmetric to ctor_b's NEQ_ZERO.
        return ("rev", _CTOR_NEQ_ZERO[ctor_b_name])
    if ctor_b_name == "Zero_t":
        return ("fwd", _CTOR_NEQ_ZERO[ctor_a_name])
    if (ctor_a_name, ctor_b_name) in CTOR_DISJOINTNESS:
        return ("fwd", CTOR_DISJOINTNESS[(ctor_a_name, ctor_b_name)])
    if (ctor_b_name, ctor_a_name) in CTOR_DISJOINTNESS:
        return ("rev", CTOR_DISJOINTNESS[(ctor_b_name, ctor_a_name)])
    raise ValueError(f"_ctor_neq_lemma: no disjointness for {ctor_a_name} vs {ctor_b_name}")


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


def derive_rec_eq(REC, target_ctor_name, var_names):
    """Constructor recursion equation, auto-generated.

    Args:
      REC : ``|- !n. F n = body[F, n]`` from ``define_wf_lt``.
      target_ctor_name : name in ``_CTORS`` (e.g. ``"Succ_t"``).
      var_names : list of strings naming the constructor's args
                  (length must match the constructor's arity).

    Returns:
      ``|- !v1...vk. F (target_C v1...vk) = <body of matching disjunct,
                                              with v1..vk substituted>``,
      with all non-matching disjuncts collapsed to F via the relevant
      ``_NEQ_*`` / ``CTOR_DISJOINTNESS`` lemmas.
    """
    if target_ctor_name not in _CTORS:
        raise ValueError(f"derive_rec_eq: unknown ctor {target_ctor_name!r}")
    target_decl = _CTORS[target_ctor_name]
    target_arity = len(target_decl[3])
    if len(var_names) != target_arity:
        raise ValueError(
            f"derive_rec_eq: {target_ctor_name} has arity {target_arity}, "
            f"got {len(var_names)} var names"
        )
    target_args = [Var(name, nat0_ty) for name in var_names]
    target_app = _ctor_app(target_decl, target_args)
    rec_at = SPEC(target_app, REC)             # |- F target_app = body[F, target_app]
    body_at = rand(rec_at._concl)
    disjuncts = _split_n_disj(body_at)

    # For each disjunct, classify and produce the |- disjunct = ... eq.
    target_inj = _CTOR_INJ.get(target_ctor_name)
    per_eqs = []
    for disj in disjuncts:
        head_name = _disjunct_ctor_name(disj)
        if head_name == target_ctor_name:
            if target_arity == 1:
                eq = _disjunct_eq_match_unary(disj, target_app, target_args[0], target_inj)
            else:
                eq = _disjunct_eq_match_binary(disj, target_app, target_args, target_inj)
        else:
            # Non-matching: collapse to F via disjointness lemma. Witnesses
            # are extracted post-CHOOSE_WITNESS inside the helper to keep
            # nested existentials' substitutions in lockstep.
            neq_dir = _ctor_neq_lemma(target_ctor_name, head_name)
            eq = _disjunct_eq_F_via_neq(disj, neq_dir, target_args)
        per_eqs.append(eq)

    body_eq = or_chain_collapse(per_eqs)        # |- body_at = collapsed_rhs
    final = TRANS(rec_at, body_eq)              # |- F target_app = collapsed_rhs
    return GENL(target_args, final)


def derive_rec_eq_pw(REC, target_ctor_name, var_names):
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
    if target_ctor_name not in _CTORS:
        raise ValueError(f"derive_rec_eq_pw: unknown ctor {target_ctor_name!r}")
    target_decl = _CTORS[target_ctor_name]
    target_arity = len(target_decl[3])
    if len(var_names) != target_arity:
        raise ValueError(
            f"derive_rec_eq_pw: {target_ctor_name} has arity {target_arity}, "
            f"got {len(var_names)} var names"
        )
    target_args = [Var(name, nat0_ty) for name in var_names]
    target_app = _ctor_app(target_decl, target_args)
    rec_at = SPEC(target_app, REC)
    # rec_at : |- fn target_app = (\v. body[fn, target_app, v])
    body_abs = rand(rec_at._concl)
    v_bvar = body_abs.bvar
    rec_at_v = AP_THM(rec_at, v_bvar)
    rhs_redex = rand(rec_at_v._concl)
    rhs_beta = BETA_CONV(rhs_redex)
    rec_normalized = TRANS(rec_at_v, rhs_beta)
    # rec_normalized : |- fn target_app v_bvar = body[fn, target_app, v_bvar]

    body_at = rand(rec_normalized._concl)
    disjuncts = _split_n_disj(body_at)
    target_inj = _CTOR_INJ.get(target_ctor_name)
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
            neq_dir = _ctor_neq_lemma(target_ctor_name, head_name)
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
    rest_th = CONJUNCT2(ASSUME(disj))                # {disj} |- rest
    disj_th = CONJ(REFL(target_app), ASSUME(rest))   # {rest} |- disj
    return DEDUCT_ANTISYM_RULE(disj_th, rest_th)


def derive_rec_eq_select(REC, target_ctor_name, var_names, extra_arg_vars):
    """Constructor recursion equation for SELECT-shaped recursion.

    Given REC : ``|- !n. fn n = (\\arg1...argk. @r. body[fn, n, args, r])``
    from ``define_wf_lt`` (where ``A = type(arg1) -> ... -> nat0`` and the
    body is a disjunction over r-values), produce
        ``|- !v1...vk arg1...argk. fn (C v1...vk) arg1...argk = R``
    where ``R`` is the matching disjunct's r-value (with witnesses
    instantiated to the constructor args).

    Supports nullary constructors via ``target_ctor_name = "Zero_t"`` and
    ``var_names = []``; the matching disjunct is then a non-existential
    conjunction (``Zero_t = Zero_t /\\ rest``). Conditional matched rests
    (``(cond /\\ r = T) \\/ (~cond /\\ r = E)``, used by ``Var_t`` and
    ``Forall_f`` in substitute) need ``derive_rec_eq_select_cond``.
    """
    if target_ctor_name == "Zero_t":
        if var_names:
            raise ValueError(
                "derive_rec_eq_select: Zero_t is nullary; var_names must "
                "be empty"
            )
        target_arity = 0
        target_args = []
        target_app = Zero_t
    else:
        if target_ctor_name not in _CTORS:
            raise ValueError(
                f"derive_rec_eq_select: unknown ctor {target_ctor_name!r}"
            )
        target_decl = _CTORS[target_ctor_name]
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
    select_term = rand(cur._concl)        # @r. body
    select_pred = select_term.arg          # \r. body  (the predicate of @)
    r_bvar = select_pred.bvar
    body_at = select_pred.body            # body[fn, target_app, args, r]
    disjuncts = _split_n_disj(body_at)

    target_inj = _CTOR_INJ.get(target_ctor_name)
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
            # The matched disjunct's RHS should be ``r = K``; pin K.
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
            neq_dir = _ctor_neq_lemma(target_ctor_name, head_name)
            eq = _disjunct_eq_F_via_neq(disj, neq_dir, target_args)
        per_eqs.append(eq)

    if matched_K is None:
        raise ValueError(
            f"derive_rec_eq_select: no matching disjunct for "
            f"{target_ctor_name}"
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


def derive_rec_eq_select_cond(REC, target_ctor_name, var_names,
                               extra_arg_vars):
    """Constructor recursion equation for SELECT-shaped recursion with
    a conditional matching disjunct.

    The matched disjunct (after INJ-witness substitution) reduces to
    ``(P /\\ r = T) \\/ (~P /\\ r = E)`` where ``P``, ``T``, ``E`` are
    expressions in the constructor args + extras. Returns the pair
    ``(THEN_TH, ELSE_TH)``:

      THEN_TH : ``|- !v1...vk extras. P  ==> fn (C v1...vk) extras = T``
      ELSE_TH : ``|- !v1...vk extras. ~P ==> fn (C v1...vk) extras = E``
    """
    if target_ctor_name not in _CTORS:
        raise ValueError(
            f"derive_rec_eq_select_cond: unknown ctor "
            f"{target_ctor_name!r}"
        )
    target_decl = _CTORS[target_ctor_name]
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

    target_inj = _CTOR_INJ.get(target_ctor_name)
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
            neq_dir = _ctor_neq_lemma(target_ctor_name, head_name)
            eq = _disjunct_eq_F_via_neq(disj, neq_dir, target_args)
        per_eqs.append(eq)

    if matched_form is None:
        raise ValueError(
            f"derive_rec_eq_select_cond: no matching disjunct for "
            f"{target_ctor_name}"
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
        return GENL(target_args + list(extra_arg_vars),
                    DISCH(hyp_t, fn_eq_K))

    THEN_TH = _build_branch(True, T_val, P_t)
    ELSE_TH = _build_branch(False, E_val, not_P_t)
    return THEN_TH, ELSE_TH


# ---------------------------------------------------------------------------
# Stage 1 (b): is_term -- "encodes a Q term" predicate.
#
# Body shape:
#   F is_term n  :=
#        n = Zero_t
#     \/ ?x. n = Succ_t x /\ is_term x
#     \/ ?x. n = Var_t x
#     \/ ?a b. n = Plus_t a b /\ is_term a /\ is_term b
#     \/ ?a b. n = Times_t a b /\ is_term a /\ is_term b
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


def _is_term_body(f_t, n_t):
    """The disjunction body of ``_is_term_F`` at terms ``f_t`` and ``n_t``."""
    return mk_or(
        mk_eq(n_t, Zero_t),
        mk_or(
            mk_exists(_x_n0, mk_and(
                mk_eq(n_t, mk_app(Succ_t, _x_n0)),
                mk_app(f_t, _x_n0),
            )),
            mk_or(
                mk_exists(_x_n0, mk_eq(n_t, mk_app(Var_t, _x_n0))),
                mk_or(
                    mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
                        mk_eq(n_t, mk_app(Plus_t, _a_n0, _b_n0)),
                        mk_and(mk_app(f_t, _a_n0), mk_app(f_t, _b_n0)),
                    ))),
                    mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
                        mk_eq(n_t, mk_app(Times_t, _a_n0, _b_n0)),
                        mk_and(mk_app(f_t, _a_n0), mk_app(f_t, _b_n0)),
                    ))),
                ),
            ),
        ),
    )


_IS_TERM_F_DEF = define(
    "_is_term_F",
    _F_pred_ty,
    mk_abs(_f_pred, mk_abs(_n_var_top, _is_term_body(_f_pred, _n_var_top))),
)
_IS_TERM_F = mk_const("_is_term_F", [])


@proof
def IS_TERM_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                  ==> _is_term_F f n = _is_term_F g n."""
    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> "
        "_is_term_F f n = _is_term_F g n",
        types={"f": _pred_ty, "g": _pred_ty,
               "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")

    h_th = p.fact("h")
    eq_zero = REFL(p._parse("n = Zero_t"))
    eq_succ = mono_iff_unary_step(Succ_t, NAT0_LT_SUCC_T, h_th)
    eq_var = REFL(p._parse("?x. n = Var_t x"))
    eq_plus = mono_iff_binary_step(
        Plus_t, NAT0_LT_PLUS_T_L, NAT0_LT_PLUS_T_R, h_th
    )
    eq_times = mono_iff_binary_step(
        Times_t, NAT0_LT_TIMES_T_L, NAT0_LT_TIMES_T_R, h_th
    )
    body_eq = or_chain_collapse(
        [eq_zero, eq_succ, eq_var, eq_plus, eq_times]
    )

    p.thus(
        "_is_term_F f n = _is_term_F g n"
    ).by_unfold(body_eq, _IS_TERM_F_DEF)


def _unfold_rec_via_F_def(rec_raw, F_def):
    """Convert ``|- !n. fn n = F fn n`` to ``|- !n. fn n = body[fn, n]``
    by unfolding the helper constant and beta-reducing its application."""
    forall_pred = dest_forall(rec_raw._concl)
    n_local = forall_pred.bvar
    spec = SPEC(n_local, rec_raw)               # |- fn n = F fn n
    rhs = rand(spec._concl)
    eq_unfold = REWRITE_CONV([F_def], rhs)      # |- F fn n = (\f n. body) fn n
    eq_beta = BETA_NORM(rand(eq_unfold._concl)) # |- (\f n. body) fn n = body[fn, n]
    rhs_eq = TRANS(eq_unfold, eq_beta)          # |- F fn n = body[fn, n]
    return GEN(n_local, TRANS(spec, rhs_eq))


IS_TERM_DEF, _IS_TERM_REC_RAW = define_wf_lt(
    "is_term",
    _pred_ty,
    _IS_TERM_F,
    IS_TERM_MONO,
)
IS_TERM_REC = _unfold_rec_via_F_def(_IS_TERM_REC_RAW, _IS_TERM_F_DEF)


# Constructor recursion equations.
IS_TERM_AT_SUCC = derive_rec_eq(IS_TERM_REC, "Succ_t", ["t"])
IS_TERM_AT_VAR = derive_rec_eq(IS_TERM_REC, "Var_t", ["v"])
IS_TERM_AT_PLUS = derive_rec_eq(IS_TERM_REC, "Plus_t", ["t1", "t2"])
IS_TERM_AT_TIMES = derive_rec_eq(IS_TERM_REC, "Times_t", ["t1", "t2"])


# ---------------------------------------------------------------------------
# Stage 1 (b): is_form -- "encodes a Q formula" predicate.
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


is_term_const = mk_const("is_term", [])


def _is_form_body(f_t, n_t):
    return mk_or(
        mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
            mk_eq(n_t, mk_app(Eq_f, _a_n0, _b_n0)),
            mk_and(mk_app(is_term_const, _a_n0),
                   mk_app(is_term_const, _b_n0)),
        ))),
        mk_or(
            mk_exists(_x_n0, mk_and(
                mk_eq(n_t, mk_app(Not_f, _x_n0)),
                mk_app(f_t, _x_n0),
            )),
            mk_or(
                mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
                    mk_eq(n_t, mk_app(Imp_f, _a_n0, _b_n0)),
                    mk_and(mk_app(f_t, _a_n0), mk_app(f_t, _b_n0)),
                ))),
                mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
                    mk_eq(n_t, mk_app(Forall_f, _a_n0, _b_n0)),
                    mk_app(f_t, _b_n0),
                ))),
            ),
        ),
    )


_IS_FORM_F_DEF = define(
    "_is_form_F",
    _F_pred_ty,
    mk_abs(_f_pred, mk_abs(_n_var_top, _is_form_body(_f_pred, _n_var_top))),
)
_IS_FORM_F = mk_const("_is_form_F", [])


@proof
def IS_FORM_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                  ==> _is_form_F f n = _is_form_F g n."""
    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> "
        "_is_form_F f n = _is_form_F g n",
        types={"f": _pred_ty, "g": _pred_ty,
               "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")

    h_th = p.fact("h")
    eq_eq = REFL(p._parse(
        "?a b. n = Eq_f a b /\\ is_term a /\\ is_term b"
    ))
    eq_not = mono_iff_unary_step(Not_f, NAT0_LT_NOT_F, h_th)
    eq_imp = mono_iff_binary_step(
        Imp_f, NAT0_LT_IMP_F_L, NAT0_LT_IMP_F_R, h_th
    )
    eq_forall = mono_iff_binary_right_step(
        Forall_f, NAT0_LT_FORALL_F_R, h_th
    )
    body_eq = or_chain_collapse(
        [eq_eq, eq_not, eq_imp, eq_forall]
    )

    p.thus(
        "_is_form_F f n = _is_form_F g n"
    ).by_unfold(body_eq, _IS_FORM_F_DEF)


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


# ---------------------------------------------------------------------------
# Stage 1 (c): free_in -- "variable index v occurs free in encoded n".
#
# Body shape (eight disjuncts; Zero_t falls through to ``F`` because no
# disjunct head matches it):
#   F free_in n  :=  \v.
#        ?x. n = Succ_t x /\ free_in x v
#     \/ ?x. n = Var_t x /\ v = x
#     \/ ?a b. n = Plus_t a b /\ (free_in a v \/ free_in b v)
#     \/ ?a b. n = Times_t a b /\ (free_in a v \/ free_in b v)
#     \/ ?a b. n = Eq_f a b /\ (free_in a v \/ free_in b v)
#     \/ ?x. n = Not_f x /\ free_in x v
#     \/ ?a b. n = Imp_f a b /\ (free_in a v \/ free_in b v)
#     \/ ?a b. n = Forall_f a b /\ ~(v = a) /\ free_in b v
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


def _free_in_body(f_t, n_t, v_t):
    """Bool body of ``_free_in_F`` at the v-applied level."""
    def _bin_disj(ctor):
        return mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
            mk_eq(n_t, mk_app(ctor, _a_n0, _b_n0)),
            mk_or(mk_app(f_t, _a_n0, v_t), mk_app(f_t, _b_n0, v_t)),
        )))

    return mk_or(
        mk_exists(_x_n0, mk_and(
            mk_eq(n_t, mk_app(Succ_t, _x_n0)),
            mk_app(f_t, _x_n0, v_t),
        )),
        mk_or(
            mk_exists(_x_n0, mk_and(
                mk_eq(n_t, mk_app(Var_t, _x_n0)),
                mk_eq(v_t, _x_n0),
            )),
            mk_or(
                _bin_disj(Plus_t),
                mk_or(
                    _bin_disj(Times_t),
                    mk_or(
                        _bin_disj(Eq_f),
                        mk_or(
                            mk_exists(_x_n0, mk_and(
                                mk_eq(n_t, mk_app(Not_f, _x_n0)),
                                mk_app(f_t, _x_n0, v_t),
                            )),
                            mk_or(
                                _bin_disj(Imp_f),
                                mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
                                    mk_eq(n_t, mk_app(Forall_f, _a_n0, _b_n0)),
                                    mk_and(
                                        mk_not(mk_eq(v_t, _a_n0)),
                                        mk_app(f_t, _b_n0, v_t),
                                    ),
                                ))),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )


_FREE_IN_F_DEF = define(
    "_free_in_F",
    _F_pred2_ty,
    mk_abs(_f_pred2, mk_abs(_n_var_top,
        mk_abs(_v_n0, _free_in_body(_f_pred2, _n_var_top, _v_n0)))),
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
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> "
        "_free_in_F f n = _free_in_F g n",
        types={"f": _pred2_ty, "g": _pred2_ty,
               "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")

    h_th = p.fact("h")

    eq_succ = mono_iff_unary_pw_step(
        Succ_t, NAT0_LT_SUCC_T, h_th, _v_n0
    )
    eq_var = REFL(p._parse("?x. n = Var_t x /\\ v = x"))
    eq_plus = mono_iff_binary_disj_pw_step(
        Plus_t, NAT0_LT_PLUS_T_L, NAT0_LT_PLUS_T_R, h_th, _v_n0
    )
    eq_times = mono_iff_binary_disj_pw_step(
        Times_t, NAT0_LT_TIMES_T_L, NAT0_LT_TIMES_T_R, h_th, _v_n0
    )
    eq_eq = mono_iff_binary_disj_pw_step(
        Eq_f, NAT0_LT_EQ_F_L, NAT0_LT_EQ_F_R, h_th, _v_n0
    )
    eq_not = mono_iff_unary_pw_step(
        Not_f, NAT0_LT_NOT_F, h_th, _v_n0
    )
    eq_imp = mono_iff_binary_disj_pw_step(
        Imp_f, NAT0_LT_IMP_F_L, NAT0_LT_IMP_F_R, h_th, _v_n0
    )
    eq_forall = mono_iff_forall_pw_step(
        NAT0_LT_FORALL_F_R, h_th, _v_n0
    )
    body_eq = or_chain_collapse([
        eq_succ, eq_var, eq_plus, eq_times,
        eq_eq, eq_not, eq_imp, eq_forall,
    ])
    # body_eq : {h_concl} |- body[f, n, v] = body[g, n, v].

    abs_eq = ABS(_v_n0, body_eq)
    # abs_eq : {h_concl} |- (\v. body[f, n, v]) = (\v. body[g, n, v]).

    p.thus(
        "_free_in_F f n = _free_in_F g n"
    ).by_unfold(abs_eq, _FREE_IN_F_DEF)


FREE_IN_DEF, _FREE_IN_REC_RAW = define_wf_lt(
    "free_in",
    _pred2_ty,
    _FREE_IN_F,
    FREE_IN_MONO,
)
FREE_IN_REC = _unfold_rec_via_F_def(_FREE_IN_REC_RAW, _FREE_IN_F_DEF)


# Constructor recursion equations (pointwise).
FREE_IN_AT_SUCC = derive_rec_eq_pw(FREE_IN_REC, "Succ_t", ["t"])
FREE_IN_AT_VAR = derive_rec_eq_pw(FREE_IN_REC, "Var_t", ["w"])
FREE_IN_AT_PLUS = derive_rec_eq_pw(FREE_IN_REC, "Plus_t", ["t1", "t2"])
FREE_IN_AT_TIMES = derive_rec_eq_pw(FREE_IN_REC, "Times_t", ["t1", "t2"])
FREE_IN_AT_EQ = derive_rec_eq_pw(FREE_IN_REC, "Eq_f", ["t1", "t2"])
FREE_IN_AT_NOT = derive_rec_eq_pw(FREE_IN_REC, "Not_f", ["phi"])
FREE_IN_AT_IMP = derive_rec_eq_pw(FREE_IN_REC, "Imp_f", ["phi1", "phi2"])
FREE_IN_AT_FORALL = derive_rec_eq_pw(FREE_IN_REC, "Forall_f", ["w", "phi"])


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
#            (n = Zero_t /\ r = Zero_t)
#         \/ (?x. n = Succ_t x /\ r = Succ_t (sub x new_t v))
#         \/ (?x. n = Var_t x
#                 /\ ((v = x  /\ r = new_t)
#                  \/ (~(v = x) /\ r = Var_t x)))
#         \/ (?a b. n = Plus_t a b
#                 /\ r = Plus_t (sub a new_t v) (sub b new_t v))
#         \/ (?a b. n = Times_t a b
#                 /\ r = Times_t (sub a new_t v) (sub b new_t v))
#         \/ (?a b. n = Eq_f a b
#                 /\ r = Eq_f (sub a new_t v) (sub b new_t v))
#         \/ (?x. n = Not_f x /\ r = Not_f (sub x new_t v))
#         \/ (?a b. n = Imp_f a b
#                 /\ r = Imp_f (sub a new_t v) (sub b new_t v))
#         \/ (?a b. n = Forall_f a b
#                 /\ ((v = a   /\ r = Forall_f a b)
#                  \/ (~(v = a) /\ r = Forall_f a (sub b new_t v))))
#   where ``sub k new_t v`` is shorthand for ``f k new_t v``.
#
# A : ``nat0 -> nat0 -> nat0`` (curry new_t and v under the recursion target).
#
# Output:
#   * SUBSTITUTE_MONO, SUBSTITUTE_DEF, SUBSTITUTE_REC.
#   * Seven non-conditional rec equations (Zero_t, Succ_t, Plus_t,
#     Times_t, Eq_f, Not_f, Imp_f) via ``derive_rec_eq_select``.
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


def _substitute_body(f_t, n_t, new_t_t, v_t, r_t):
    """Bool body of the @r-disjunction inside ``_substitute_F``."""
    def fc(arg):
        return mk_app(f_t, arg, new_t_t, v_t)

    return mk_or(
        mk_and(mk_eq(n_t, Zero_t), mk_eq(r_t, Zero_t)),
        mk_or(
            mk_exists(_x_n0, mk_and(
                mk_eq(n_t, mk_app(Succ_t, _x_n0)),
                mk_eq(r_t, mk_app(Succ_t, fc(_x_n0))),
            )),
            mk_or(
                mk_exists(_x_n0, mk_and(
                    mk_eq(n_t, mk_app(Var_t, _x_n0)),
                    mk_or(
                        mk_and(mk_eq(v_t, _x_n0), mk_eq(r_t, new_t_t)),
                        mk_and(mk_not(mk_eq(v_t, _x_n0)),
                               mk_eq(r_t, mk_app(Var_t, _x_n0))),
                    ),
                )),
                mk_or(
                    mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
                        mk_eq(n_t, mk_app(Plus_t, _a_n0, _b_n0)),
                        mk_eq(r_t, mk_app(Plus_t, fc(_a_n0), fc(_b_n0))),
                    ))),
                    mk_or(
                        mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
                            mk_eq(n_t, mk_app(Times_t, _a_n0, _b_n0)),
                            mk_eq(r_t, mk_app(Times_t, fc(_a_n0), fc(_b_n0))),
                        ))),
                        mk_or(
                            mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
                                mk_eq(n_t, mk_app(Eq_f, _a_n0, _b_n0)),
                                mk_eq(r_t, mk_app(Eq_f, fc(_a_n0), fc(_b_n0))),
                            ))),
                            mk_or(
                                mk_exists(_x_n0, mk_and(
                                    mk_eq(n_t, mk_app(Not_f, _x_n0)),
                                    mk_eq(r_t, mk_app(Not_f, fc(_x_n0))),
                                )),
                                mk_or(
                                    mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
                                        mk_eq(n_t, mk_app(Imp_f, _a_n0, _b_n0)),
                                        mk_eq(r_t,
                                              mk_app(Imp_f,
                                                     fc(_a_n0),
                                                     fc(_b_n0))),
                                    ))),
                                    mk_exists(_a_n0, mk_exists(_b_n0, mk_and(
                                        mk_eq(n_t,
                                              mk_app(Forall_f, _a_n0, _b_n0)),
                                        mk_or(
                                            mk_and(
                                                mk_eq(v_t, _a_n0),
                                                mk_eq(r_t,
                                                      mk_app(Forall_f,
                                                             _a_n0, _b_n0)),
                                            ),
                                            mk_and(
                                                mk_not(mk_eq(v_t, _a_n0)),
                                                mk_eq(r_t,
                                                      mk_app(Forall_f,
                                                             _a_n0,
                                                             fc(_b_n0))),
                                            ),
                                        ),
                                    ))),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )


_SUBSTITUTE_F_DEF = define(
    "_substitute_F",
    _F_pred3_ty,
    mk_abs(_f_pred3, mk_abs(_n_var_top, mk_abs(_new_t_n0, mk_abs(_v_n0,
        mk_select(_r_n0,
                  _substitute_body(_f_pred3, _n_var_top, _new_t_n0,
                                   _v_n0, _r_n0)))))),
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
        types={"f": _pred3_ty, "g": _pred3_ty,
               "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")

    h_th = p.fact("h")
    args = [_new_t_n0, _v_n0]

    n_t = p._parse("n")
    eq_zero = REFL(mk_and(mk_eq(n_t, Zero_t), mk_eq(_r_n0, Zero_t)))
    eq_succ = mono_iff_value_unary_pw_step(
        Succ_t, NAT0_LT_SUCC_T, h_th, args, _r_n0,
        lambda t: mk_app(Succ_t, t),
    )
    eq_var = REFL(mk_exists(_x_n0, mk_and(
        mk_eq(n_t, mk_app(Var_t, _x_n0)),
        mk_or(
            mk_and(mk_eq(_v_n0, _x_n0), mk_eq(_r_n0, _new_t_n0)),
            mk_and(mk_not(mk_eq(_v_n0, _x_n0)),
                   mk_eq(_r_n0, mk_app(Var_t, _x_n0))),
        ),
    )))
    eq_plus = mono_iff_value_binary_pw_step(
        Plus_t, NAT0_LT_PLUS_T_L, NAT0_LT_PLUS_T_R, h_th, args, _r_n0,
        lambda a, b: mk_app(Plus_t, a, b),
    )
    eq_times = mono_iff_value_binary_pw_step(
        Times_t, NAT0_LT_TIMES_T_L, NAT0_LT_TIMES_T_R, h_th, args, _r_n0,
        lambda a, b: mk_app(Times_t, a, b),
    )
    eq_eq = mono_iff_value_binary_pw_step(
        Eq_f, NAT0_LT_EQ_F_L, NAT0_LT_EQ_F_R, h_th, args, _r_n0,
        lambda a, b: mk_app(Eq_f, a, b),
    )
    eq_not = mono_iff_value_unary_pw_step(
        Not_f, NAT0_LT_NOT_F, h_th, args, _r_n0,
        lambda t: mk_app(Not_f, t),
    )
    eq_imp = mono_iff_value_binary_pw_step(
        Imp_f, NAT0_LT_IMP_F_L, NAT0_LT_IMP_F_R, h_th, args, _r_n0,
        lambda a, b: mk_app(Imp_f, a, b),
    )
    eq_forall = mono_iff_forall_value_pw_step(
        NAT0_LT_FORALL_F_R, h_th, args, _r_n0, _v_n0,
    )

    body_eq = or_chain_collapse([
        eq_zero, eq_succ, eq_var, eq_plus, eq_times,
        eq_eq, eq_not, eq_imp, eq_forall,
    ])
    # body_eq : {h_concl} |- body[f, n, new_t, v, r] = body[g, n, new_t, v, r]

    abs_r_eq = ABS(_r_n0, body_eq)
    # abs_r_eq : ... |- (\r. body[f]) = (\r. body[g])
    sel_const = mk_const("@", [(nat0_ty, _aty_for_select())])
    select_eq = AP_TERM(sel_const, abs_r_eq)
    # select_eq : ... |- (@r. body[f]) = (@r. body[g])
    abs_v_eq = ABS(_v_n0, select_eq)
    abs_nt_eq = ABS(_new_t_n0, abs_v_eq)
    # abs_nt_eq : ... |- (\new_t v. @r. body[f]) = (\new_t v. @r. body[g])

    p.thus(
        "_substitute_F f n = _substitute_F g n"
    ).by_unfold(abs_nt_eq, _SUBSTITUTE_F_DEF)


SUBSTITUTE_DEF, _SUBSTITUTE_REC_RAW = define_wf_lt(
    "substitute",
    _pred3_ty,
    _SUBSTITUTE_F,
    SUBSTITUTE_MONO,
)
SUBSTITUTE_REC = _unfold_rec_via_F_def(
    _SUBSTITUTE_REC_RAW, _SUBSTITUTE_F_DEF
)


# Constructor recursion equations.
#
# Seven cases reduce to a single ``r = K`` shape and use
# ``derive_rec_eq_select``. The two conditional cases (Var_t and
# Forall_f) collapse to ``(cond /\ r = T) \/ (~cond /\ r = E)`` and
# use ``derive_rec_eq_select_cond`` to produce a pair of conditional
# rec equations (``cond ==> rhs = T`` and ``~cond ==> rhs = E``).
SUBSTITUTE_AT_ZERO = derive_rec_eq_select(
    SUBSTITUTE_REC, "Zero_t", [], [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_SUCC = derive_rec_eq_select(
    SUBSTITUTE_REC, "Succ_t", ["t"], [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_PLUS = derive_rec_eq_select(
    SUBSTITUTE_REC, "Plus_t", ["t1", "t2"], [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_TIMES = derive_rec_eq_select(
    SUBSTITUTE_REC, "Times_t", ["t1", "t2"], [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_EQ = derive_rec_eq_select(
    SUBSTITUTE_REC, "Eq_f", ["t1", "t2"], [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_NOT = derive_rec_eq_select(
    SUBSTITUTE_REC, "Not_f", ["phi"], [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_IMP = derive_rec_eq_select(
    SUBSTITUTE_REC, "Imp_f", ["phi1", "phi2"], [_new_t_n0, _v_n0],
)
# Conditional cases: each yields a HIT (cond branch) and MISS (~cond
# branch) recursion equation.
SUBSTITUTE_AT_VAR_HIT, SUBSTITUTE_AT_VAR_MISS = derive_rec_eq_select_cond(
    SUBSTITUTE_REC, "Var_t", ["x"], [_new_t_n0, _v_n0],
)
SUBSTITUTE_AT_FORALL_HIT, SUBSTITUTE_AT_FORALL_MISS = derive_rec_eq_select_cond(
    SUBSTITUTE_REC, "Forall_f", ["a", "b"], [_new_t_n0, _v_n0],
)


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
    print("Stage 1 -- MONO helpers (per-disjunct iffs).")
    # Smoke test: build a fake hypothesis ASSUME(!k. nat0_lt k n ==> f k = g k)
    # and exercise both helpers against the q_syntax constructors.
    from axioms import mk_forall, mk_imp
    from basics import mk_app as _mk_app
    _f_smoke = Var("f", parse_type("nat0 -> bool"))
    _g_smoke = Var("g", parse_type("nat0 -> bool"))
    _n_smoke = Var("n", nat0_ty)
    _k_smoke = Var("k", nat0_ty)
    _nat0_lt_const = mk_const("nat0_lt", [])
    _smoke_hyp = ASSUME(mk_forall(_k_smoke, mk_imp(
        _mk_app(_nat0_lt_const, _k_smoke, _n_smoke),
        mk_eq(_mk_app(_f_smoke, _k_smoke), _mk_app(_g_smoke, _k_smoke)),
    )))
    _IFF_SUCC_T = mono_iff_unary_step(Succ_t, NAT0_LT_SUCC_T, _smoke_hyp)
    _IFF_PLUS_T = mono_iff_binary_step(
        Plus_t, NAT0_LT_PLUS_T_L, NAT0_LT_PLUS_T_R, _smoke_hyp,
    )
    print("  unary  (Succ_t):", pp_thm(_IFF_SUCC_T))
    print("  binary (Plus_t):", pp_thm(_IFF_PLUS_T))
    print()
    print("Stage 1 -- derive_rec_eq smoke test (synthetic recursive body).")
    # Synthetic predicate F : nat0 -> bool with body matching is_term shape.
    _F_pred = Var("F", parse_type("nat0 -> bool"))
    _n_var = Var("n", nat0_ty)
    _t_smoke = Var("t", nat0_ty)
    _v_smoke = Var("v", nat0_ty)
    _a_smoke = Var("a", nat0_ty)
    _b_smoke = Var("b", nat0_ty)
    _body = mk_or(
        mk_eq(_n_var, Zero_t),
        mk_or(
            mk_exists(_t_smoke, mk_and(
                mk_eq(_n_var, _mk_app(Succ_t, _t_smoke)),
                _mk_app(_F_pred, _t_smoke),
            )),
            mk_or(
                mk_exists(_v_smoke, mk_eq(_n_var, _mk_app(Var_t, _v_smoke))),
                mk_exists(_a_smoke, mk_exists(_b_smoke, mk_and(
                    mk_eq(_n_var, _mk_app(Plus_t, _a_smoke, _b_smoke)),
                    mk_and(_mk_app(_F_pred, _a_smoke), _mk_app(_F_pred, _b_smoke)),
                ))),
            ),
        ),
    )
    _fake_REC = ASSUME(mk_forall(_n_var, mk_eq(_mk_app(_F_pred, _n_var), _body)))
    _REC_SUCC = derive_rec_eq(_fake_REC, "Succ_t", ["t"])
    _REC_VAR  = derive_rec_eq(_fake_REC, "Var_t", ["v"])
    _REC_PLUS = derive_rec_eq(_fake_REC, "Plus_t", ["a", "b"])
    print("  REC at Succ_t :", pp_thm(_REC_SUCC))
    print("  REC at Var_t  :", pp_thm(_REC_VAR))
    print("  REC at Plus_t :", pp_thm(_REC_PLUS))
    print()
    print("Stage 1 (b) -- is_term predicate.")
    print("    _IS_TERM_F_DEF :", pp_thm(_IS_TERM_F_DEF))
    print("    IS_TERM_MONO   :", pp_thm(IS_TERM_MONO))
    print("    IS_TERM_DEF    :", pp_thm(IS_TERM_DEF))
    print("    IS_TERM_REC    :", pp_thm(IS_TERM_REC))
    print("    IS_TERM_AT_SUCC  :", pp_thm(IS_TERM_AT_SUCC))
    print("    IS_TERM_AT_VAR   :", pp_thm(IS_TERM_AT_VAR))
    print("    IS_TERM_AT_PLUS  :", pp_thm(IS_TERM_AT_PLUS))
    print("    IS_TERM_AT_TIMES :", pp_thm(IS_TERM_AT_TIMES))
    print()
    print("Stage 1 (b) -- is_form predicate.")
    print("    IS_FORM_MONO   :", pp_thm(IS_FORM_MONO))
    print("    IS_FORM_DEF    :", pp_thm(IS_FORM_DEF))
    print("    IS_FORM_REC    :", pp_thm(IS_FORM_REC))
    print("    IS_FORM_AT_EQ     :", pp_thm(IS_FORM_AT_EQ))
    print("    IS_FORM_AT_NOT    :", pp_thm(IS_FORM_AT_NOT))
    print("    IS_FORM_AT_IMP    :", pp_thm(IS_FORM_AT_IMP))
    print("    IS_FORM_AT_FORALL :", pp_thm(IS_FORM_AT_FORALL))
    print()
    print("Stage 1 (c) -- free_in predicate.")
    print("    FREE_IN_MONO   :", pp_thm(FREE_IN_MONO))
    print("    FREE_IN_DEF    :", pp_thm(FREE_IN_DEF))
    print("    FREE_IN_REC    :", pp_thm(FREE_IN_REC))
    print("    FREE_IN_AT_SUCC   :", pp_thm(FREE_IN_AT_SUCC))
    print("    FREE_IN_AT_VAR    :", pp_thm(FREE_IN_AT_VAR))
    print("    FREE_IN_AT_PLUS   :", pp_thm(FREE_IN_AT_PLUS))
    print("    FREE_IN_AT_TIMES  :", pp_thm(FREE_IN_AT_TIMES))
    print("    FREE_IN_AT_EQ     :", pp_thm(FREE_IN_AT_EQ))
    print("    FREE_IN_AT_NOT    :", pp_thm(FREE_IN_AT_NOT))
    print("    FREE_IN_AT_IMP    :", pp_thm(FREE_IN_AT_IMP))
    print("    FREE_IN_AT_FORALL :", pp_thm(FREE_IN_AT_FORALL))
    print()
    print("Stage 1 (c) -- substitute.")
    print("    SUBSTITUTE_MONO         :", pp_thm(SUBSTITUTE_MONO))
    print("    SUBSTITUTE_DEF          :", pp_thm(SUBSTITUTE_DEF))
    print("    SUBSTITUTE_REC          :", pp_thm(SUBSTITUTE_REC))
    print("    SUBSTITUTE_AT_ZERO      :", pp_thm(SUBSTITUTE_AT_ZERO))
    print("    SUBSTITUTE_AT_SUCC      :", pp_thm(SUBSTITUTE_AT_SUCC))
    print("    SUBSTITUTE_AT_VAR_HIT   :", pp_thm(SUBSTITUTE_AT_VAR_HIT))
    print("    SUBSTITUTE_AT_VAR_MISS  :", pp_thm(SUBSTITUTE_AT_VAR_MISS))
    print("    SUBSTITUTE_AT_PLUS      :", pp_thm(SUBSTITUTE_AT_PLUS))
    print("    SUBSTITUTE_AT_TIMES     :", pp_thm(SUBSTITUTE_AT_TIMES))
    print("    SUBSTITUTE_AT_EQ        :", pp_thm(SUBSTITUTE_AT_EQ))
    print("    SUBSTITUTE_AT_NOT       :", pp_thm(SUBSTITUTE_AT_NOT))
    print("    SUBSTITUTE_AT_IMP       :", pp_thm(SUBSTITUTE_AT_IMP))
    print("    SUBSTITUTE_AT_FORALL_HIT :", pp_thm(SUBSTITUTE_AT_FORALL_HIT))
    print("    SUBSTITUTE_AT_FORALL_MISS:", pp_thm(SUBSTITUTE_AT_FORALL_MISS))
