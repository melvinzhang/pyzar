# ---------------------------------------------------------------------------
# Stage 3 -- representability in HF.
# ---------------------------------------------------------------------------
#
# A predicate P : nat0 -> bool is *represented* in HF by a-formula
# F(x) -- with var_x as its sole free variable -- iff
#
#     |- !n. P n      ==> Prov_HF (substitute F (numeral n) var_x)
#     |- !n. ~ P n    ==> Prov_HF (Not_f (substitute F (numeral n) var_x))
#
# A function f : nat0 -> nat0 is represented by a HF-formula F(x, y) iff
#
#     |- !n. Prov_HF (substitute_2 F (numeral n) (numeral (f n)) var_x var_y)
#     |- !n. Prov_HF (Forall_f var_y
#                      (Imp_f (substitute_2 F (numeral n) y var_x var_y)
#                             (Eq_f y (numeral (f n))))).
#
# We need representability of three specific predicates:
#
#   (i)   ``Proof_HF_set`` (the HF-native proof-checking predicate).
#   (ii)  ``substitute``  (primitive recursive on godelnums).
#   (iii) ``godelnum``    (identity on encoded syntax; its numeral
#                          image is what matters).
#
# The active provability route is dependency-set finite HF proof objects
# via ``Proof_HF_set``; ``Prov_HF`` is defined from that predicate, not
# from lists.
#

from fusion import Var
from basics import mk_const, mk_app, mk_abs, rand, rator
from parser import add_const, define, parse, parse_type
from axioms import mk_forall, mk_imp, mk_not, mk_and, mk_or, mk_exists
from nat0 import nat0_ty, define_unary_0, mk_suc0, ZERO, AXIOM_3_0, AXIOM_4_0
from nat0_order import define_wf_lt
from proof import proof, define_with_at
from tactics import (
    SPEC,
    SPECL,
    GEN,
    SYM,
    TRANS,
    DISJ1,
    DISJ2,
    REFL,
    EQ_MP,
    MP,
    CONJ,
    CONJUNCT1,
    CONJUNCT2,
    NOT_INTRO,
    DISCH,
    NOT_ELIM,
    EQF_INTRO,
    CONTR,
)
from fusion import ASSUME
from basics import mk_eq

from hf_syntax import (
    Var_t,  # noqa: F401  -- parser alias for generated HF formulas
    Eq_f,  # noqa: F401  -- parser alias for generated HF formulas
    Not_f,  # noqa: F401  -- parser alias for generated HF formulas
    Imp_f,  # noqa: F401  -- parser alias for generated HF formulas
    Forall_f,  # noqa: F401  -- parser alias for generated HF formulas
    Insert_t,
    Empty_t,
    In_a,  # noqa: F401  -- parser alias for generated HF formulas
    IS_TERM_REC,
    IS_FORM_REC,
    IS_TERM_AT_INSERT,
    SUBSTITUTE_AT_EMPTY,
    SUBSTITUTE_AT_VAR_HIT,
    SUBSTITUTE_AT_VAR_MISS,
    SUBSTITUTE_AT_INSERT,
    SUBSTITUTE_AT_NOT,
    SUBSTITUTE_AT_IMP,
    SUBSTITUTE_AT_EQ,
    SUBSTITUTE_AT_FORALL_HIT,
    SUBSTITUTE_AT_FORALL_MISS,
    SUBSTITUTE_AT_IN,
    NAT0_LT_NOT_F,
    NAT0_LT_INSERT_T_L,
    NAT0_LT_INSERT_T_R,
    NAT0_LT_EQ_F_L,
    NAT0_LT_EQ_F_R,
    NAT0_LT_IMP_F_L,
    NAT0_LT_IMP_F_R,
    NAT0_LT_FORALL_F_R,
    NAT0_LT_IN_A_L,
    NAT0_LT_IN_A_R,
    _unfold_rec_via_F_def,
    _mono_iff_value_binary_pw_step,
)
from hf_qsyntax import qparse
from hf_sets import (
    In,  # noqa: F401  -- parser alias for HF proof-object predicates
    Pair_ord,  # noqa: F401  -- parser alias for HF proof-object predicates
    Insert,  # noqa: F401  -- parser alias for quote_hf bridge
    Empty,  # noqa: F401  -- parser alias for quote_hf bridge
    Singleton,  # noqa: F401  -- parser alias for QUOTE_HF_AT_SINGLETON
    Pair,  # noqa: F401  -- parser alias for QUOTE_HF_AT_PAIR
    Pair_ord,  # noqa: F401  -- parser alias for QUOTE_HF_AT_PAIR_ORD
    Union,  # noqa: F401  -- parser alias for proof-object union witnesses
    EMPTY_DEF,  # used by QUOTE_HF_AT_EMPTY to fold Empty into 0
    INSERT_AT,  # used by QUOTE_HF_AT_INSERT_LOW to unfold Insert to set_bit
    SINGLETON_AS_INSERT,  # quote_hf Singleton bridge
    LOW_BIT_SINGLETON,  # quote_hf Pair / Pair_ord bridge
    SINGLETON_LT_PAIR,  # quote_hf Pair_ord bridge
    PAIR_AT,  # used by QUOTE_HF_AT_PAIR to unfold Pair to Insert
    PAIR_ORD_AT,  # used by QUOTE_HF_AT_PAIR_ORD to unfold Pair_ord
    IN_INSERT_SAME,
    IN_INSERT_DIFF,
    IN_UNION,
    IN_PAIR,
    IN_SINGLETON,
    NOT_IN_EMPTY,
    PAIR_ORD_INJ,
    NAT0_LT_PAIR_ORD_L,
    NAT0_LT_PAIR_ORD_R,
)
from bits import (  # noqa: E402 -- canonical low-bit decomposition for quote_hf
    low_bit,
    clear_low,
    LOW_BIT_LT,
    CLEAR_LOW_LT,
    COND_T_NAT0,
    COND_F_NAT0,
    LOW_BIT_SET_BIT_NEW,
    CLEAR_LOW_SET_BIT_NEW,
    SET_BIT_NZ,
    INSERT_LOW_BIT_CLEAR_LOW,
    LOW_BIT_CLEAR_LOW_PRECOND,
)
from classical import (  # noqa: E402 -- COND machinery for quote_hf body
    mk_cond,
    EXCLUDED_MIDDLE,
)
from tactics import EQT_INTRO, EQF_INTRO  # noqa: E402,F401  -- used in QUOTE_HF_MONO/_AT_NZ
from tactics import REWRITE_RULE, REWRITE_PROVE
from fusion import vsubst, aty, new_axiom
from hf_proof import (
    var_x,
    VAR_X_DEF,
    var_y,
    VAR_Y_DEF,
    var_z,
    VAR_Z_DEF,
    is_axiom,
    is_hf_axiom,
    is_hf_ind_axiom,
    is_mp,
    is_gen,
    IS_MP_AT,
    IS_GEN_AT,
    IS_REFL_AT,
    IS_LOGICAL_AXIOM_AT,
    IS_AXIOM_AT,
)


# ---------------------------------------------------------------------------
# Stage 3A (a) -- the numeral function (von Neumann ordinals).
#
#   numeral 0          =  Empty_t.
#   numeral (SUC0 n)   =  Insert_t (numeral n) (numeral n).
#
# Following Świerczkowski (2003), numerals are encoded as von Neumann
# ordinals inside HF: 0 := empty set, n+1 := n ∪ {n}, and ``n ∪ {n}``
# is exactly ``Insert n n`` in the HF Insert-as-adjoin convention.
#
# ``numeral n`` is a closed HF-term; its Goedel number is itself a
# closed nat0 numeral (a deeply nested Pair_ord tree) under hf_syntax's
# Pair_ord-flat encoding.
# ---------------------------------------------------------------------------


_n_n0 = Var("n", nat0_ty)
_a_n0 = Var("a", nat0_ty)


# Step body: \k a. Insert_t a a.  (k unused; the new value is the von
# Neumann successor of the recursive result.)
_h_numeral = mk_abs(_n_n0, mk_abs(_a_n0, mk_app(Insert_t, _a_n0, _a_n0)))


NUMERAL_BASE, NUMERAL_STEP = define_unary_0(
    "numeral",
    parse_type("nat0 -> nat0"),
    Empty_t,
    _h_numeral,
    result_ty=nat0_ty,
)
numeral = mk_const("numeral", [])


# ---------------------------------------------------------------------------
# Stage 3A (b) -- IS_TERM_NUMERAL: every numeral is a well-formed HF term.
#
#   |- !n. is_term (numeral n).
#
# Direct induction on n. The base case ``is_term Empty_t`` follows from
# IS_TERM_REC's leftmost disjunct ``n = Empty_t`` via REFL. The step
# case uses IS_TERM_AT_INSERT applied to the diagonal pair
# ``(numeral n, numeral n)`` with the inductive hypothesis used twice.
# ---------------------------------------------------------------------------


is_term = mk_const("is_term", [])


@proof
def IS_TERM_EMPTY(p):
    """|- is_term Empty_t.

    From IS_TERM_REC at Empty_t the body's leftmost disjunct
    ``Empty_t = Empty_t`` is reflexive; lift via DISJ1 and EQ_MP
    through SYM.
    """
    p.goal("is_term Empty_t")

    rec_at_empty = SPEC(Empty_t, IS_TERM_REC)
    rhs = rand(rec_at_empty._concl)
    refl_empty = REFL(Empty_t)
    from basics import rand as _rand

    rest = _rand(rhs)
    rhs_th = DISJ1(refl_empty, rest)
    p.thus("is_term Empty_t").by_eq_mp(SYM(rec_at_empty), rhs_th)


@proof
def IS_TERM_INSERT(p):
    """|- !t1 t2. is_term t1 /\\ is_term t2 ==> is_term (Insert_t t1 t2).

    ``IS_TERM_AT_INSERT`` from Stage 1 reduces the Insert-disjunct of the
    body to ``is_term t1 /\\ is_term t2``; one EQ_MP step.
    """
    p.goal("!t1 t2. is_term t1 /\\ is_term t2 ==> is_term (Insert_t t1 t2)")
    p.fix("t1 t2")
    p.assume("ih: is_term t1 /\\ is_term t2")
    at_insert = SPECL([p._parse("t1"), p._parse("t2")], IS_TERM_AT_INSERT)
    p.thus("is_term (Insert_t t1 t2)").by_eq_mp(SYM(at_insert), "ih")


@proof
def IS_TERM_NUMERAL(p):
    """|- !n. is_term (numeral n)."""
    p.goal("!n. is_term (numeral n)")
    p.fix("n")
    with p.induction("n"):
        with p.base():
            p.have("eq0: numeral 0 = Empty_t").by_thm(NUMERAL_BASE)
            p.thus("is_term (numeral 0)").by_rewrite_of(
                IS_TERM_EMPTY, [SYM(p.fact("eq0"))]
            )
        with p.step("IH"):
            p.have(
                "eq_step: numeral (SUC0 n) = Insert_t (numeral n) (numeral n)"
            ).by(NUMERAL_STEP, "n")
            ih_pair = CONJ(p.fact("IH"), p.fact("IH"))
            p.have(
                "ins_term: is_term (Insert_t (numeral n) (numeral n))"
            ).by(IS_TERM_INSERT, "numeral n", "numeral n", ih_pair)
            p.thus("is_term (numeral (SUC0 n))").by_rewrite_of(
                "ins_term", [SYM(p.fact("eq_step"))]
            )


# ---------------------------------------------------------------------------
# Stage 3A (c) -- shared constants and helpers used by Stage 3B and beyond.
#
# ``substitute`` and ``Not_f`` are referenced by name from this point on;
# the ``represents_pred`` scaffolding (which mentions ``Prov_HF``) lives
# in Stage 3B (m) below, after ``Prov_HF`` has been defined as the
# set-native Sigma_1 form ``\n. ?P. Proof_HF_set P n``.
# ---------------------------------------------------------------------------


substitute = mk_const("substitute", [])
Not_f = mk_const("Not_f", [])


_F_n0 = Var("F", nat0_ty)
_P_pred = Var("P", parse_type("nat0 -> bool"))


def _subst_at_numeral(F_term, n_term):
    """Build ``substitute F (numeral n) 0`` -- substitute the F-slot
    variable (index 0, encoded ``var_x = Var_t 0``) in ``F`` with the
    numeral encoding of n.
    """
    return mk_app(substitute, F_term, mk_app(numeral, n_term), ZERO)


# ---------------------------------------------------------------------------
# Stage 3B (set-native target) -- dependency-set HF proof objects.
#
# This is the intended representation for ``Prov_HF_internal``. A proof
# object ``P`` is a finite HF set of records ``Pair_ord k h`` where ``k``
# is the step's finite dependency set and ``h`` is the formula proved at
# that record. A record with dependency set ``k`` may cite only records
# whose ranks are members of ``k``. Since HF membership is well-founded
# under the Ackermann encoding, this preserves the "earlier proof step"
# discipline without introducing an internal arithmetic ``lt`` relation.
#
# The definitions here are external HOL predicates. The HF-formula bodies
# for the corresponding internal predicates are the next bridge work in
# ``hf_sorry.md``.
# ---------------------------------------------------------------------------


VALID_STEP_HF_SET_DEF, VALID_STEP_HF_SET_AT = define_with_at(
    "valid_step_hf_set",
    parse_type("nat0 -> nat0 -> nat0 -> bool"),
    "\\P:nat0. \\k:nat0. \\h:nat0. "
    "is_axiom h "
    "\\/ (?i f j g. In (Pair_ord i f) P /\\ In (Pair_ord j g) P "
    "      /\\ In i k /\\ In j k /\\ is_mp f g h) "
    "\\/ (?i f. In (Pair_ord i f) P /\\ In i k /\\ is_gen f h)",
)
valid_step_hf_set = mk_const("valid_step_hf_set", [])


PROOF_HF_SET_DEF, PROOF_HF_SET_AT = define_with_at(
    "Proof_HF_set",
    parse_type("nat0 -> nat0 -> bool"),
    "\\P:nat0. \\n:nat0. "
    "?k. In (Pair_ord k n) P "
    "    /\\ (!j h. In (Pair_ord j h) P ==> valid_step_hf_set P j h)",
)
Proof_HF_set = mk_const("Proof_HF_set", [])


# ---------------------------------------------------------------------------
# Stage 3B (j) -- set-native Sigma_1 definition of Prov_HF.
#
#   Prov_HF n  :<=>  ?P. Proof_HF_set P n.
#
# This is the canonical HF-native form: provability is the existence of
# a dependency-set finite HF proof object.
# ---------------------------------------------------------------------------


# |- !n. Prov_HF n = (?P. Proof_HF_set P n).
PROV_HF_DEF, PROV_HF_AT = define_with_at(
    "Prov_HF",
    parse_type("nat0 -> bool"),
    "\\n:nat0. ?P:nat0. Proof_HF_set P n",
)
Prov_HF = mk_const("Prov_HF", [])


# ---------------------------------------------------------------------------
# Stage 3B (k/l) closure rules for ``Prov_HF`` live below the
# HF-set proof-object prototypes, because the Python proof decorators
# need ``AXIOM_HAS_PROOF_HF_SET``, ``MP_HAS_PROOF_HF_SET``, and
# ``GEN_HAS_PROOF_HF_SET`` to exist before the closure proof functions
# are defined.
# ---------------------------------------------------------------------------


# Stage 3B (m) -- representability scaffolding.
#
# A unary predicate ``P : nat0 -> bool`` is *represented* by a
# HF-formula ``F`` (a nat0 godelnum, taken to be a HF-formula whose only
# free variable is ``var_x``) iff:
#
#   * (positive)  !n. P n      ==> Prov_HF (substitute F (numeral n) var_x).
#   * (negative)  !n. ~ P n    ==> Prov_HF (Not_f (substitute F (numeral n) var_x)).
#
# We package the conjunction of the two conditions as
# ``represents_pred F P``. Defined here, after ``Prov_HF``.
# ---------------------------------------------------------------------------


_pos_clause = mk_forall(
    _n_n0,
    mk_imp(mk_app(_P_pred, _n_n0), mk_app(Prov_HF, _subst_at_numeral(_F_n0, _n_n0))),
)
_neg_clause = mk_forall(
    _n_n0,
    mk_imp(
        mk_not(mk_app(_P_pred, _n_n0)),
        mk_app(Prov_HF, mk_app(Not_f, _subst_at_numeral(_F_n0, _n_n0))),
    ),
)

_represents_pred_body = mk_and(_pos_clause, _neg_clause)

# |- !F P. represents_pred F P =
#          ((!n. P n ==> Prov_HF (substitute F (numeral n) var_x))
#        /\ (!n. ~ P n
#               ==> Prov_HF (Not_f (substitute F (numeral n) var_x)))).
REPRESENTS_PRED_DEF, REPRESENTS_PRED_AT = define_with_at(
    "represents_pred",
    parse_type("nat0 -> (nat0 -> bool) -> bool"),
    mk_abs(_F_n0, mk_abs(_P_pred, _represents_pred_body)),
)
represents_pred = mk_const("represents_pred", [])


# ---------------------------------------------------------------------------
# Stage 3C (a) -- representability of ``substitute``.
#
# Headline theorem for formula consumers:
#   |- !F t v. is_form F ==> Prov_HF (
#         substitute (substitute (substitute (substitute
#             substitute_internal (quote_hf F) var_x)
#             (quote_hf t) var_y)
#             (quote_hf v) var_z)
#             (quote_hf (substitute F t v)) var_w).
#
# ``substitute_internal`` is a HF-formula in four free variables --
# ``var_x`` (F-slot), ``var_y`` (t-slot), ``var_z`` (v-slot), ``var_w``
# (result-slot) -- expressing the relation "substitute(F, t, v) = r".
#
# Why a single fixed formula (not a HOL-recursive family): the
# diagonal lemma (Stage 3D) forms the Goedel sentence by substituting a
# numeric godelnum into a *single fixed* internal-provability formula.
# Without ``substitute_internal`` as one fixed HF-formula, no ``D(x, y)``
# represents the diagonal function and the fixed-point construction
# collapses.
#
# Encoding strategy: ``substitute_internal`` is governed by the scoped
# ``HF_SYNTAX_REC_PACKAGE`` definitional extension. The package gives
# constructor-local HF proof rules for Empty/Var/Insert/Eq/In/Not/Imp/Forall
# and derives representability for syntactic inputs. Malformed nat0 values
# intentionally have no fake substitution semantics; consumers use the
# ``SUBSTITUTE_REPRESENTS_FORM`` / ``_TERM`` wrappers.
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Variable-index constants ``idx_x``, ``idx_y``, ... -- the *indices*
# (small nat0 numerals 0, 1, 2, ...) of HF-syntax variables, distinct
# from the *encodings* ``var_x = Var_t 0``, ``var_y = Var_t 1``, ... .
#
# Convention (matches ``hf_proof.is_UI`` and the SUBSTITUTE_AT_VAR_HIT/
# MISS recursion equations):
#   * Inside an HF formula body, a free variable is referenced by its
#     encoding -- e.g. ``var_x = Var_t 0`` for the F-slot in
#     ``substitute_internal``.
#   * The third argument to ``substitute`` (and the first to ``Forall_f``)
#     is the variable's *index*, not its encoding -- so substitute calls
#     pass ``idx_x = 0``, not ``var_x = Var_t 0``.
#
# Stage 3 representability theorems thread these consistently:
# ``substitute F (numeral n) idx_x`` substitutes the variable named x
# in F with (numeral n).
# ---------------------------------------------------------------------------


IDX_X_DEF = define("idx_x", parse_type("nat0"), "0")
idx_x = mk_const("idx_x", [])

IDX_Y_DEF = define("idx_y", parse_type("nat0"), "SUC0 0")
idx_y = mk_const("idx_y", [])

IDX_Z_DEF = define("idx_z", parse_type("nat0"), "SUC0 (SUC0 0)")
idx_z = mk_const("idx_z", [])

IDX_W_DEF = define("idx_w", parse_type("nat0"), "SUC0 (SUC0 (SUC0 0))")
idx_w = mk_const("idx_w", [])


VAR_W_DEF = define("var_w", parse_type("nat0"), "Var_t (SUC0 (SUC0 (SUC0 0)))")
var_w = mk_const("var_w", [])


# var_T -- spare HF-internal bound variable at index 4. The four free slots
# var_x/y/z/w (indices 0..3) are reserved for the substitute input/output
# tuple (F, t, v, r).
VAR_T_DEF = define(
    "var_T",
    parse_type("nat0"),
    "Var_t (SUC0 (SUC0 (SUC0 (SUC0 0))))",
)
var_T = mk_const("var_T", [])

IDX_T_DEF = define("idx_T", parse_type("nat0"), "SUC0 (SUC0 (SUC0 (SUC0 0)))")
idx_T = mk_const("idx_T", [])


# Additional HF-internal variables reserved for generated syntax-recursion
# rules:
#   var_a, var_b           -- generic constructor slots / binders.
#   var_s1, var_s2         -- Not_f sub-shape existentials.
#   var_wq                 -- Var_t-miss / Forall_f-* index existentials
#                             (named with q-suffix to avoid clash with HOL w).
#   var_a1, var_a2,        -- binary-constructor sub-shape existentials.
#   var_b1, var_b2
#   var_f1, var_f2         -- Forall_f-miss body existentials.
# Indices 5..14 of the HF-variable namespace; the matching index
# constants ``idx_a``, ``idx_b``, ... live alongside.
def _var_q_def(name, idx):
    suc = "0"
    for _ in range(idx):
        suc = f"(SUC0 {suc})"
    return define(name, parse_type("nat0"), f"Var_t {suc}")


def _idx_q_def(name, idx):
    suc = "0"
    for _ in range(idx):
        suc = f"(SUC0 {suc})"
    return define(name, parse_type("nat0"), suc)


VAR_A_DEF = _var_q_def("var_a", 5)
var_a = mk_const("var_a", [])
IDX_A_DEF = _idx_q_def("idx_a", 5)
idx_a = mk_const("idx_a", [])
VAR_B_DEF = _var_q_def("var_b", 6)
var_b = mk_const("var_b", [])
IDX_B_DEF = _idx_q_def("idx_b", 6)
idx_b = mk_const("idx_b", [])
VAR_S1_DEF = _var_q_def("var_s1", 7)
var_s1 = mk_const("var_s1", [])
VAR_S2_DEF = _var_q_def("var_s2", 8)
var_s2 = mk_const("var_s2", [])
VAR_WQ_DEF = _var_q_def("var_wq", 9)
var_wq = mk_const("var_wq", [])
VAR_A1_DEF = _var_q_def("var_a1", 10)
var_a1 = mk_const("var_a1", [])
VAR_A2_DEF = _var_q_def("var_a2", 11)
var_a2 = mk_const("var_a2", [])
VAR_B1_DEF = _var_q_def("var_b1", 12)
var_b1 = mk_const("var_b1", [])
VAR_B2_DEF = _var_q_def("var_b2", 13)
var_b2 = mk_const("var_b2", [])
VAR_F1_DEF = _var_q_def("var_f1", 14)
var_f1 = mk_const("var_f1", [])
VAR_F2_DEF = _var_q_def("var_f2", 15)
var_f2 = mk_const("var_f2", [])


# HF-encoding macros at the Python level. HF has only Forall_f, Imp_f, Not_f,
# Eq_f as primitives -- everything else is hand-encoded. Build HF-formulas
# compositionally rather than spelling out the Not_f/Imp_f/Forall_f tree
# literally (which would balloon any large HF-formula by 10x).
def Q_and(a, b):
    """HF's /\\ as Not_f (Imp_f a (Not_f b))."""
    return mk_app(Not_f, mk_app(Imp_f, a, mk_app(Not_f, b)))


def Q_or(a, b):
    """HF's \\/ as Imp_f (Not_f a) b."""
    return mk_app(Imp_f, mk_app(Not_f, a), b)


def Q_imp(a, b):
    """HF's ==> -- Imp_f a b."""
    return mk_app(Imp_f, a, b)


def Q_not(a):
    return mk_app(Not_f, a)


def Q_eq(a, b):
    return mk_app(Eq_f, a, b)


def Q_neq(a, b):
    return Q_not(Q_eq(a, b))


def Q_forall(idx, body):
    """HF's !x. body  --  Forall_f idx body  (idx is the raw nat0 index)."""
    return mk_app(Forall_f, idx, body)


def Q_exists(idx, body):
    """HF's ?x. body  --  Not_f (Forall_f idx (Not_f body))."""
    return Q_not(Q_forall(idx, Q_not(body)))


def Q_and_chain(*xs):
    """Right-associated /\\ chain."""
    if not xs:
        raise ValueError("Q_and_chain: need at least one term")
    out = xs[-1]
    for x in reversed(xs[:-1]):
        out = Q_and(x, out)
    return out


def Q_or_chain(*xs):
    """Right-associated \\/ chain."""
    if not xs:
        raise ValueError("Q_or_chain: need at least one term")
    out = xs[-1]
    for x in reversed(xs[:-1]):
        out = Q_or(x, out)
    return out


def Q_exists_chain(idxs, body):
    """Nested HF-exists ``?idx0 idx1 ... . body``."""
    out = body
    for idx in reversed(idxs):
        out = Q_exists(idx, out)
    return out


# Raw nat0 indices (NOT the Var_t-wrapped term forms) used as the
# binder-position arguments for Q_forall / Q_exists. ``var_*`` (Var_t k)
# is the *term* form -- referenced inside formula bodies; the binder
# position takes just ``k``. Build them once so the encoding code below
# can splice them as needed.
def _idx_term(k):
    suc = ZERO
    for _ in range(k):
        suc = mk_suc0(suc)
    return suc


# ---------------------------------------------------------------------------
# Substitute-pushing lemmas for the HF-encoding macros.
#
# Q_not / Q_imp / Q_eq / Q_forall coincide with their primitive HOL
# constructors (Not_f / Imp_f / Eq_f / Forall_f), so the existing
# SUBSTITUTE_AT_NOT / _IMP / _EQ / _FORALL_HIT / _FORALL_MISS already
# push substitute through them -- no new lemma needed.
#
# Q_and / Q_or / Q_neq / Q_exists desugar into composite Not_f / Imp_f /
# Forall_f trees. Each lemma below packages the multi-step push of
# substitute through the literal expansion into a single named theorem
# usable as a one-shot ``by_rewrite`` rule when reducing
# ``substitute (Q_macro ...) new_t v`` symbolically inside
# representability proofs.
#
# These are all unconditional (Q_and / Q_or / Q_neq) or split into HIT /
# MISS branches by the binder side condition (Q_exists). Each is a
# one-line composition of SUBSTITUTE_AT_NOT / _IMP / _EQ / _FORALL_*.
# ---------------------------------------------------------------------------


@proof
def SUBSTITUTE_AND(p):
    """|- !a b new_t v.
            substitute (Not_f (Imp_f a (Not_f b))) new_t v
            = Not_f (Imp_f (substitute a new_t v)
                           (Not_f (substitute b new_t v))).

    Q_and a b = Not_f (Imp_f a (Not_f b)); pushes substitute through
    the outer Not_f, the Imp_f, and the inner Not_f wrapping b.
    """
    p.goal(
        "!a b new_t v. "
        "substitute (Not_f (Imp_f a (Not_f b))) new_t v "
        "= Not_f (Imp_f (substitute a new_t v) "
        "               (Not_f (substitute b new_t v)))"
    )
    p.fix("a b new_t v")
    p.thus(
        "substitute (Not_f (Imp_f a (Not_f b))) new_t v "
        "= Not_f (Imp_f (substitute a new_t v) "
        "               (Not_f (substitute b new_t v)))"
    ).by_rewrite([SUBSTITUTE_AT_NOT, SUBSTITUTE_AT_IMP])


@proof
def SUBSTITUTE_OR(p):
    """|- !a b new_t v.
            substitute (Imp_f (Not_f a) b) new_t v
            = Imp_f (Not_f (substitute a new_t v))
                    (substitute b new_t v).

    Q_or a b = Imp_f (Not_f a) b; substitute pushes through the Imp_f
    and the Not_f wrapping a.
    """
    p.goal(
        "!a b new_t v. "
        "substitute (Imp_f (Not_f a) b) new_t v "
        "= Imp_f (Not_f (substitute a new_t v)) "
        "        (substitute b new_t v)"
    )
    p.fix("a b new_t v")
    p.thus(
        "substitute (Imp_f (Not_f a) b) new_t v "
        "= Imp_f (Not_f (substitute a new_t v)) "
        "        (substitute b new_t v)"
    ).by_rewrite([SUBSTITUTE_AT_NOT, SUBSTITUTE_AT_IMP])


@proof
def SUBSTITUTE_NEQ(p):
    """|- !a b new_t v.
            substitute (Not_f (Eq_f a b)) new_t v
            = Not_f (Eq_f (substitute a new_t v)
                          (substitute b new_t v)).

    Q_neq a b = Not_f (Eq_f a b); substitute pushes through the outer
    Not_f and the Eq_f.
    """
    p.goal(
        "!a b new_t v. "
        "substitute (Not_f (Eq_f a b)) new_t v "
        "= Not_f (Eq_f (substitute a new_t v) "
        "              (substitute b new_t v))"
    )
    p.fix("a b new_t v")
    p.thus(
        "substitute (Not_f (Eq_f a b)) new_t v "
        "= Not_f (Eq_f (substitute a new_t v) "
        "              (substitute b new_t v))"
    ).by_rewrite([SUBSTITUTE_AT_NOT, SUBSTITUTE_AT_EQ])


@proof
def SUBSTITUTE_EXISTS_HIT(p):
    """|- !idx body new_t v. v = idx ==>
            substitute (Not_f (Forall_f idx (Not_f body))) new_t v
            = Not_f (Forall_f idx (Not_f body)).

    Q_exists idx body = Not_f (Forall_f idx (Not_f body)); when v
    equals the binder index, the inner Forall_f hits and substitute
    halts: the body is unchanged.
    """
    p.goal(
        "!idx body new_t v. v = idx ==> "
        "substitute (Not_f (Forall_f idx (Not_f body))) new_t v "
        "= Not_f (Forall_f idx (Not_f body))"
    )
    p.fix("idx body new_t v")
    p.assume("hv: v = idx")
    forall_hit_at = SPECL(
        [
            p._parse("idx"),
            p._parse("Not_f body"),
            p._parse("new_t"),
            p._parse("v"),
        ],
        SUBSTITUTE_AT_FORALL_HIT,
    )
    forall_hit_app = MP(forall_hit_at, p.fact("hv"))
    p.thus(
        "substitute (Not_f (Forall_f idx (Not_f body))) new_t v "
        "= Not_f (Forall_f idx (Not_f body))"
    ).by_rewrite([SUBSTITUTE_AT_NOT, forall_hit_app])


@proof
def SUBSTITUTE_EXISTS_MISS(p):
    """|- !idx body new_t v. ~(v = idx) ==>
            substitute (Not_f (Forall_f idx (Not_f body))) new_t v
            = Not_f (Forall_f idx (Not_f (substitute body new_t v))).

    Q_exists idx body = Not_f (Forall_f idx (Not_f body)); when v
    differs from the binder index, substitute pushes through the outer
    Not_f, the Forall_f (capture-free under v != idx), and the inner
    Not_f wrapping body.
    """
    p.goal(
        "!idx body new_t v. ~(v = idx) ==> "
        "substitute (Not_f (Forall_f idx (Not_f body))) new_t v "
        "= Not_f (Forall_f idx (Not_f (substitute body new_t v)))"
    )
    p.fix("idx body new_t v")
    p.assume("hne: ~(v = idx)")
    forall_miss_at = SPECL(
        [
            p._parse("idx"),
            p._parse("Not_f body"),
            p._parse("new_t"),
            p._parse("v"),
        ],
        SUBSTITUTE_AT_FORALL_MISS,
    )
    forall_miss_app = MP(forall_miss_at, p.fact("hne"))
    p.thus(
        "substitute (Not_f (Forall_f idx (Not_f body))) new_t v "
        "= Not_f (Forall_f idx (Not_f (substitute body new_t v)))"
    ).by_rewrite([SUBSTITUTE_AT_NOT, forall_miss_app])


_idx_x = ZERO  # var_x = Var_t 0   (F slot)
_idx_y = mk_suc0(ZERO)  # var_y = Var_t 1   (t slot)
_idx_z = mk_suc0(mk_suc0(ZERO))  # var_z = Var_t 2   (v slot)
_idx_w = mk_suc0(mk_suc0(mk_suc0(ZERO)))  # var_w = Var_t 3   (r slot)
_idx_T = _idx_term(4)
_idx_a = _idx_term(5)
_idx_b = _idx_term(6)
_idx_s1 = _idx_term(7)
_idx_s2 = _idx_term(8)
_idx_wq = _idx_term(9)
_idx_a1 = _idx_term(10)
_idx_a2 = _idx_term(11)
_idx_b1 = _idx_term(12)
_idx_b2 = _idx_term(13)
_idx_f1 = _idx_term(14)
_idx_f2 = _idx_term(15)


# ---------------------------------------------------------------------------
# Substitute representability now uses the syntax-recursion package below.
# The old finite-computation proof route has been removed from this module.

# ===========================================================================
# HF-encoding side.
#
# Each ``is_X_internal`` is the HF-formula encoding of the HOL predicate
# ``X``. The associated ``IS_X_REPRESENTS`` theorem says: at every input
# where the HOL fact holds, HF proves the substituted HF-formula.
#
# Encoding strategy -- quote_hf bridge:
#
#   HOL HF sets are bit-encoded (``Insert i s = set_bit i s``); HF-syntax
#   HF sets are Insert_t-tower-encoded (``Insert_t i s = Pair_ord 9
#   (Pair_ord i s)``). The two are different nat0 functions. To make
#   HF's axioms HF1-HF5 (which speak about Insert_t / Empty_t) apply
#   to HOL-witnessed HF facts, we bridge at the goal interface via
#
#       quote_hf : nat0 -> nat0   -- bit-encoded HF set -> Insert_t-tower.
#
#   Every HF-set input slot in a representability goal uses ``quote_hf``.
#   The ``SUBSTITUTE_REPRESENTS`` headline uses ``quote_hf`` for the F /
#   t / v / r slots. Syntax codes are already HF sets; using ``numeral``
#   would convert the code to an ordinal and lose the constructor shape.
#   The IS_*_REPRESENTS lemmas also use ``quote_hf`` throughout since
#   their inputs are HF-shaped encoded sets and members.
# ===========================================================================


# quote_hf bridge (the encoding interface).
#
# HOL ``Insert`` (bit-encoded) and HF-syntax ``Insert_t`` (Pair_ord-tagged)
# are different nat0 functions; ``quote_hf`` recursively rebuilds an HF
# set as an Insert_t-tower of nat0-element-encoded children. The result
# is Insert-tower-shaped from HF's perspective, so HF1-HF3 fire on
# membership / non-membership queries directly.
#
# Recursion structure (canonical low-bit-first form):
#   quote_hf 0  = Empty_t.
#   quote_hf n  = Insert_t (quote_hf (low_bit n)) (quote_hf (clear_low n))
#                  for n != 0.
#       (Decomposition is deterministic: each non-empty set is split
#        on its lowest set bit. ``low_bit n`` and ``clear_low n`` are
#        both < n under nat0_lt, so the recursion is well-founded.)
#
# Concrete construction: well-founded recursion on ``nat0_lt`` via
# ``define_wf_lt`` with body
#
#     F f n = COND (n = 0) Empty_t
#                  (Insert_t (f (low_bit n)) (f (clear_low n))).
#
# A literal ``~In i s ==> quote_hf (Insert i s) = Insert_t (quote_hf i)
# (quote_hf s)`` for *arbitrary* fresh ``i`` is HOL-inconsistent under
# ``Insert_t`` injectivity, so downstream consumers walk the canonical
# (low-bit-first) structure instead.
_quote_hf_fn_ty = parse_type("nat0 -> nat0")
_quote_hf_F_ty = parse_type("(nat0 -> nat0) -> nat0 -> nat0")
_f_qhf = Var("f", _quote_hf_fn_ty)
_g_qhf = Var("g", _quote_hf_fn_ty)
_n_qhf = Var("n", nat0_ty)


def _quote_hf_body(f_t, n_t):
    """Body of ``_quote_hf_F`` at the n-applied level."""
    return mk_cond(
        mk_eq(n_t, ZERO),
        Empty_t,
        mk_app(
            Insert_t,
            mk_app(f_t, mk_app(low_bit, n_t)),
            mk_app(f_t, mk_app(clear_low, n_t)),
        ),
    )


_QUOTE_HF_F_DEF = define(
    "_quote_hf_F",
    _quote_hf_F_ty,
    mk_abs(_f_qhf, mk_abs(_n_qhf, _quote_hf_body(_f_qhf, _n_qhf))),
)
_QUOTE_HF_F = mk_const("_quote_hf_F", [])


@proof
def QUOTE_HF_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                  ==> _quote_hf_F f n = _quote_hf_F g n.

    Value-valued MONO. Build the body equation
        ``body[f, n] = body[g, n]``
    by case-split on ``n = 0`` (T branch: COND collapses both to
    Empty_t; F branch: f/g agree at low_bit n / clear_low n via the
    hypothesis + LOW_BIT_LT / CLEAR_LOW_LT, so by_rewrite chains them
    through the Insert_t branch). ``by_unfold`` then folds the body
    equation back to the F-level via _QUOTE_HF_F_DEF.
    """
    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) "
        "==> _quote_hf_F f n = _quote_hf_F g n",
        types={
            "f": _quote_hf_fn_ty,
            "g": _quote_hf_fn_ty,
            "n": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")

    body_eq_str = (
        "COND_nat0 (n = 0) Empty_t (Insert_t (f (low_bit n)) (f (clear_low n))) "
        "= COND_nat0 (n = 0) Empty_t (Insert_t (g (low_bit n)) (g (clear_low n)))"
    )

    with p.have(f"body_eq: {body_eq_str}").proof():
        with p.cases_on(EXCLUDED_MIDDLE, "n = 0"):
            with p.case("hz: n = 0"):
                p.have("hz_eq: (n = 0) = T").by(EQT_INTRO, "hz")
                p.thus(body_eq_str).by_rewrite(["hz_eq", COND_T_NAT0])
            with p.case("hnz: ~(n = 0)"):
                p.have("hnz_eq: (n = 0) = F").by(EQF_INTRO, "hnz")
                p.have("lb_lt: nat0_lt (low_bit n) n").by(LOW_BIT_LT, "n", "hnz")
                p.have("cl_lt: nat0_lt (clear_low n) n").by(
                    CLEAR_LOW_LT, "n", "hnz"
                )
                p.have("f_lb_eq: f (low_bit n) = g (low_bit n)").by(
                    "h", "low_bit n", "lb_lt"
                )
                p.have("f_cl_eq: f (clear_low n) = g (clear_low n)").by(
                    "h", "clear_low n", "cl_lt"
                )
                p.thus(body_eq_str).by_rewrite(
                    ["hnz_eq", COND_F_NAT0, "f_lb_eq", "f_cl_eq"]
                )

    p.thus("_quote_hf_F f n = _quote_hf_F g n").by_unfold(
        p.fact("body_eq"), _QUOTE_HF_F_DEF
    )


QUOTE_HF_DEF, _QUOTE_HF_REC_RAW = define_wf_lt(
    "quote_hf",
    _quote_hf_fn_ty,
    _QUOTE_HF_F,
    QUOTE_HF_MONO,
)
quote_hf = mk_const("quote_hf", [])

# |- !n. quote_hf n =
#        COND (n = 0) Empty_t (Insert_t (quote_hf (low_bit n))
#                                       (quote_hf (clear_low n))).
QUOTE_HF_REC = _unfold_rec_via_F_def(_QUOTE_HF_REC_RAW, _QUOTE_HF_F_DEF)


# --------------------------------------------------------------------------
# The public quote_hf interface.
#
# Stage 3 representability proofs interact with quote_hf through exactly
# two equations: ``QUOTE_HF_AT_EMPTY`` and ``QUOTE_HF_AT_INSERT_LOW``
# (plus the derived structural rewrites SINGLETON / PAIR / PAIR_ORD).
#
# The bit-level recursion equation ``_QUOTE_HF_AT_NZ`` is internal --
# it exposes ``low_bit`` / ``clear_low``, which Stage 3 proofs must
# never reference. ``_QUOTE_HF_F_DEF``, ``QUOTE_HF_MONO``,
# ``QUOTE_HF_DEF``, and ``QUOTE_HF_REC`` are likewise private to the
# definition site.
# --------------------------------------------------------------------------


@proof
def QUOTE_HF_AT_EMPTY(p):
    """|- quote_hf Empty = Empty_t.

    Specialise QUOTE_HF_REC at 0; the ``(0 = 0) = T`` branch of the
    body collapses to ``Empty_t`` via COND_T_NAT0. EMPTY_DEF folds the
    LHS from ``quote_hf 0`` to ``quote_hf Empty``.
    """
    p.goal("quote_hf Empty = Empty_t")
    p.have("zero_eq_zero: (0 = 0) = T").by_thm(EQT_INTRO(REFL(ZERO)))
    rec_at_0 = SPEC(ZERO, QUOTE_HF_REC)
    # rec_at_0 : |- quote_hf 0 = COND (0 = 0) Empty_t (Insert_t ...)
    p.thus("quote_hf Empty = Empty_t").by_rewrite_of(
        rec_at_0, [EMPTY_DEF, "zero_eq_zero", COND_T_NAT0]
    )


@proof
def _QUOTE_HF_AT_NZ(p):
    """|- !n. ~(n = 0) ==>
              quote_hf n = Insert_t (quote_hf (low_bit n))
                                     (quote_hf (clear_low n)).

    INTERNAL — exposes the bit-level low_bit / clear_low recursion.
    Stage 3 consumers should use ``QUOTE_HF_AT_INSERT_LOW`` (and the
    derived structural rewrites in section "Stage 3B (l)") instead;
    those keep the user-facing surface free of bit-decomposition.

    Specialise QUOTE_HF_REC at n; under ``~(n = 0)`` the body collapses
    via ``(n = 0) = F`` + COND_F_NAT0 to the Insert_t branch. This is
    the canonical low-bit decomposition equation: it replaces the
    inconsistent ``~In i s ==> quote_hf (Insert i s) = Insert_t ...``
    form. Downstream consumers walk this via QUOTE_HF_AT_INSERT_LOW.
    """
    p.goal(
        "!n. ~(n = 0) ==> "
        "quote_hf n = Insert_t (quote_hf (low_bit n)) (quote_hf (clear_low n))"
    )
    p.fix("n")
    p.assume("hnz: ~(n = 0)")
    p.have("hnz_eq: (n = 0) = F").by(EQF_INTRO, "hnz")
    rec_at_n = SPEC(p._parse("n"), QUOTE_HF_REC)
    # rec_at_n : |- quote_hf n = COND (n = 0) Empty_t (Insert_t ...)
    p.thus(
        "quote_hf n = Insert_t (quote_hf (low_bit n)) (quote_hf (clear_low n))"
    ).by_rewrite_of(rec_at_n, ["hnz_eq", COND_F_NAT0])


@proof
def QUOTE_HF_AT_INSERT_LOW(p):
    """|- !i s. (s = 0 \\/ nat0_lt i (low_bit s)) ==>
                quote_hf (Insert i s) = Insert_t (quote_hf i) (quote_hf s).

    Bridge from HOL HF Insert to HF-syntax Insert_t, in the canonical
    low-bit-first form. The precondition pins ``Insert i s = set_bit i s``
    to the canonical decomposition where ``low_bit (Insert i s) = i`` and
    ``clear_low (Insert i s) = s``, so _QUOTE_HF_AT_NZ collapses to the
    structural form. A precondition-free version is HOL-inconsistent under
    Insert_t injectivity (a set with two Insert decompositions would force
    its quote_hf image into two distinct Insert_t-trees).
    """
    p.goal(
        "!i s. (s = 0 \\/ nat0_lt i (low_bit s)) ==> "
        "quote_hf (Insert i s) = Insert_t (quote_hf i) (quote_hf s)"
    )
    p.fix("i s")
    p.assume("h: s = 0 \\/ nat0_lt i (low_bit s)")
    # Insert i s = set_bit i s.
    p.have("h_set: Insert i s = set_bit i s").by(INSERT_AT, "i", "s")
    # Non-zero: SET_BIT_NZ is unconditional.
    p.have("h_nz_sb: ~(set_bit i s = 0)").by(SET_BIT_NZ, "i", "s")
    p.have("h_nz: ~(Insert i s = 0)").by_rewrite_of(
        "h_nz_sb", [SYM(p.fact("h_set"))]
    )
    # Canonical decomposition matches the structural one under the precondition.
    p.have("h_lb_sb: low_bit (set_bit i s) = i").by(
        LOW_BIT_SET_BIT_NEW, "i", "s", "h"
    )
    p.have("h_lb: low_bit (Insert i s) = i").by_rewrite_of(
        "h_lb_sb", [SYM(p.fact("h_set"))]
    )
    p.have("h_cl_sb: clear_low (set_bit i s) = s").by(
        CLEAR_LOW_SET_BIT_NEW, "i", "s", "h"
    )
    p.have("h_cl: clear_low (Insert i s) = s").by_rewrite_of(
        "h_cl_sb", [SYM(p.fact("h_set"))]
    )
    # Specialise _QUOTE_HF_AT_NZ at (Insert i s) and discharge the non-zero
    # side condition; rewrite the canonical args back to (i, s).
    rec_nz = SPEC(p._parse("Insert i s"), _QUOTE_HF_AT_NZ)
    p.have(
        "h_rec: quote_hf (Insert i s) = "
        "Insert_t (quote_hf (low_bit (Insert i s))) "
        "(quote_hf (clear_low (Insert i s)))"
    ).by(rec_nz, "h_nz")
    p.thus(
        "quote_hf (Insert i s) = Insert_t (quote_hf i) (quote_hf s)"
    ).by_rewrite_of("h_rec", ["h_lb", "h_cl"])


# ---------------------------------------------------------------------------
# Stage 3B (l) -- quote_hf structural rewrites.
#
# Derived shape equations layered on top of QUOTE_HF_AT_INSERT_LOW. Each
# tells the user what ``quote_hf`` does to a derived HF-set shape
# (Singleton / Pair / ...) without ever mentioning the bit
# decomposition (low_bit / clear_low). Stage 3 representability proofs
# rewrite at the top of these and then never reach for _QUOTE_HF_AT_NZ.
# ---------------------------------------------------------------------------


@proof
def QUOTE_HF_AT_SINGLETON(p):
    """|- !x. quote_hf (Singleton x) = Insert_t (quote_hf x) Empty_t.

    ``Singleton x = Insert x Empty`` (SINGLETON_AS_INSERT) collapses the
    LHS via QUOTE_HF_AT_INSERT_LOW with precondition ``Empty = 0`` (left
    disjunct, EMPTY_DEF). The recursive call on ``Empty`` is closed by
    QUOTE_HF_AT_EMPTY.
    """
    p.goal("!x. quote_hf (Singleton x) = Insert_t (quote_hf x) Empty_t")
    p.fix("x")
    with p.have("h_pre: Empty = 0 \\/ nat0_lt x (low_bit Empty)").proof():
        p.disj(EMPTY_DEF)
    p.have(
        "h_at: quote_hf (Insert x Empty) = "
        "Insert_t (quote_hf x) (quote_hf Empty)"
    ).by(QUOTE_HF_AT_INSERT_LOW, "x", "Empty", "h_pre")
    p.thus("quote_hf (Singleton x) = Insert_t (quote_hf x) Empty_t").by_rewrite(
        [SINGLETON_AS_INSERT, "h_at", QUOTE_HF_AT_EMPTY]
    )


@proof
def QUOTE_HF_AT_PAIR(p):
    """|- !x y. nat0_lt x y ==>
                quote_hf (Pair x y) =
                Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t).

    Pair x y = Insert x (Singleton y) (PAIR_AT). QUOTE_HF_AT_INSERT_LOW
    precondition ``Singleton y = 0 \\/ nat0_lt x (low_bit (Singleton y))``
    collapses to ``nat0_lt x y`` via LOW_BIT_SINGLETON. The recursive
    call on ``Singleton y`` is folded by QUOTE_HF_AT_SINGLETON.

    The unconditional version is HOL-inconsistent: ``Pair x x =
    Singleton x`` collapses to a one-layer Insert_t-tower, while the
    RHS shown is a two-layer tower; the side condition ``nat0_lt x y``
    rules this case out.
    """
    from tactics import SYM

    p.goal(
        "!x y. nat0_lt x y ==> "
        "quote_hf (Pair x y) = "
        "Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t)"
    )
    p.fix("x y")
    p.assume("hxy: nat0_lt x y")
    with p.have(
        "h_pre: Singleton y = 0 \\/ nat0_lt x (low_bit (Singleton y))"
    ).proof():
        p.have(
            "hxly: nat0_lt x (low_bit (Singleton y))"
        ).by_rewrite_of("hxy", [LOW_BIT_SINGLETON])
        p.disj("hxly")
    p.have(
        "h_at: quote_hf (Insert x (Singleton y)) = "
        "Insert_t (quote_hf x) (quote_hf (Singleton y))"
    ).by(QUOTE_HF_AT_INSERT_LOW, "x", "Singleton y", "h_pre")
    p.thus(
        "quote_hf (Pair x y) = "
        "Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t)"
    ).by_rewrite([PAIR_AT, "h_at", QUOTE_HF_AT_SINGLETON])


@proof
def QUOTE_HF_AT_PAIR_ORD(p):
    """|- !x y. nat0_lt x y ==>
                quote_hf (Pair_ord x y) =
                Insert_t (Insert_t (quote_hf x) Empty_t)
                         (Insert_t
                            (Insert_t (quote_hf x)
                                      (Insert_t (quote_hf y) Empty_t))
                            Empty_t).

    Keystone Pair_ord shape rewrite: every HF-syntax constructor
    (``Var_t``, ``Eq_f``, ``Not_f``, ``Imp_f``, ``Forall_f``,
    ``Insert_t``, ``In_a``) is a tagged Pair_ord at the HOL level, so
    Stage 3 representability proofs collapse their goal terms via this
    lemma + the constructor's defining ``_AT`` equation, picking the
    tag-vs-arg ordering that satisfies the precondition.

    Proof: ``Pair_ord x y = Insert (Singleton x) (Singleton (Pair x y))``
    (PAIR_ORD_AT, PAIR_AT, SINGLETON_AS_INSERT). Apply
    QUOTE_HF_AT_INSERT_LOW at the outer Insert with side condition
    ``nat0_lt (Singleton x) (low_bit (Singleton (Pair x y)))`` =
    ``nat0_lt (Singleton x) (Pair x y)`` (LOW_BIT_SINGLETON), which is
    SINGLETON_LT_PAIR under ``nat0_lt x y``. The inner Pair x y is
    folded via QUOTE_HF_AT_PAIR; the singletons via QUOTE_HF_AT_SINGLETON.

    The unconditional version is HOL-inconsistent: ``Pair_ord x x =
    Singleton (Singleton x)`` collapses to a one-layer-deeper Insert_t-
    tower, while the RHS shown is the full Kuratowski two-element
    tower.
    """
    from tactics import SYM

    p.goal(
        "!x y. nat0_lt x y ==> "
        "quote_hf (Pair_ord x y) = "
        "Insert_t (Insert_t (quote_hf x) Empty_t) "
        "         (Insert_t "
        "            (Insert_t (quote_hf x) "
        "                      (Insert_t (quote_hf y) Empty_t)) "
        "            Empty_t)"
    )
    p.fix("x y")
    p.assume("hxy: nat0_lt x y")
    # Outer-Insert precondition: nat0_lt (Singleton x) (low_bit (Singleton (Pair x y))).
    p.have(
        "h_lt_sp: nat0_lt (Singleton x) (Pair x y)"
    ).by(SINGLETON_LT_PAIR, "x", "y", "hxy")
    with p.have(
        "h_pre: Singleton (Pair x y) = 0 "
        "\\/ nat0_lt (Singleton x) (low_bit (Singleton (Pair x y)))"
    ).proof():
        p.have(
            "h_lt: nat0_lt (Singleton x) (low_bit (Singleton (Pair x y)))"
        ).by_rewrite_of("h_lt_sp", [LOW_BIT_SINGLETON])
        p.disj("h_lt")
    p.have(
        "h_outer: quote_hf (Insert (Singleton x) (Singleton (Pair x y))) = "
        "Insert_t (quote_hf (Singleton x)) (quote_hf (Singleton (Pair x y)))"
    ).by(
        QUOTE_HF_AT_INSERT_LOW,
        "Singleton x",
        "Singleton (Pair x y)",
        "h_pre",
    )
    p.have(
        "h_pair: quote_hf (Pair x y) = "
        "Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t)"
    ).by(QUOTE_HF_AT_PAIR, "x", "y", "hxy")
    # Pair_ord x y = Pair (Singleton x) (Pair x y) [PAIR_ORD_AT]
    #              = Insert (Singleton x) (Singleton (Pair x y))
    #                [PAIR_AT at outer + SINGLETON_AS_INSERT].
    with p.calc(
        "quote_hf (Pair_ord x y)", thus=True
    ) as c:
        c.step(
            "= quote_hf (Insert (Singleton x) (Singleton (Pair x y)))"
        ).by_rewrite([PAIR_ORD_AT, PAIR_AT, SINGLETON_AS_INSERT])
        c.step(
            "= Insert_t (quote_hf (Singleton x)) "
            "           (quote_hf (Singleton (Pair x y)))"
        ).by_thm(p.fact("h_outer"))
        c.step(
            "= Insert_t (Insert_t (quote_hf x) Empty_t) "
            "           (Insert_t (quote_hf (Pair x y)) Empty_t)"
        ).by_rewrite([QUOTE_HF_AT_SINGLETON])
        c.step(
            "= Insert_t (Insert_t (quote_hf x) Empty_t) "
            "           (Insert_t "
            "              (Insert_t (quote_hf x) "
            "                        (Insert_t (quote_hf y) Empty_t)) "
            "              Empty_t)"
        ).by_rewrite(["h_pair"])


# ---------------------------------------------------------------------------
# Stage 3B (l) -- structural induction on HF sets.
#
# The keystone of the thin-bridge layer. Stage 3 representability proofs
# proceed by induction on the Insert-tower shape of the HF set; this
# principle packages the bit-level recursion of ``quote_hf`` into a
# user-facing form whose only references to bits.py are inside the
# canonical-form precondition (``s = 0 \\/ nat0_lt i (low_bit s)``).
# Consumers do NOT need to reach for ``low_bit`` / ``clear_low`` again
# in their own proofs.
# ---------------------------------------------------------------------------


@proof
def HF_INDUCTION(p):
    """|- !P. P Empty
              /\\ (!i s. (s = 0 \\/ nat0_lt i (low_bit s))
                         ==> P s ==> P (Insert i s))
              ==> !s. P s.

    Strong induction on ``s`` via ``nat0_lt``. In the ``s = 0`` branch
    ``P s`` collapses to ``P Empty`` via EMPTY_DEF and the base case
    discharges. In the ``s != 0`` branch:

      * ``s = set_bit (low_bit s) (clear_low s)`` (INSERT_LOW_BIT_CLEAR_LOW),
        i.e. ``s = Insert (low_bit s) (clear_low s)`` after INSERT_AT.
      * The canonical-form precondition ``clear_low s = 0 \\/
        nat0_lt (low_bit s) (low_bit (clear_low s))`` holds
        (LOW_BIT_CLEAR_LOW_PRECOND).
      * ``CLEAR_LOW_LT`` gives ``nat0_lt (clear_low s) s``, so the IH
        fires at ``clear_low s`` to yield ``P (clear_low s)``.
      * The step assumption then produces
        ``P (Insert (low_bit s) (clear_low s)) = P s``.
    """
    p.goal(
        "!P. P Empty "
        "/\\ (!i s. (s = 0 \\/ nat0_lt i (low_bit s)) "
        "          ==> P s ==> P (Insert i s)) "
        "==> !s. P s",
        types={
            "P": parse_type("nat0 -> bool"),
            "s": nat0_ty,
            "i": nat0_ty,
        },
    )
    p.fix("P")
    p.assume(
        "(base, step): "
        "P Empty "
        "/\\ (!i s. (s = 0 \\/ nat0_lt i (low_bit s)) "
        "          ==> P s ==> P (Insert i s))"
    )
    with p.strong_induction("s", "IH"):
        with p.cases_on(EXCLUDED_MIDDLE, "s = 0"):
            with p.case("hz: s = 0"):
                p.thus("P s").by_rewrite_of("base", ["hz", EMPTY_DEF])
            with p.case("hnz: ~(s = 0)"):
                p.have(
                    "h_recon_sb: s = set_bit (low_bit s) (clear_low s)"
                ).by(INSERT_LOW_BIT_CLEAR_LOW, "s", "hnz")
                p.have(
                    "h_in_sb: Insert (low_bit s) (clear_low s) "
                    "= set_bit (low_bit s) (clear_low s)"
                ).by(INSERT_AT, "low_bit s", "clear_low s")
                p.have(
                    "h_recon: s = Insert (low_bit s) (clear_low s)"
                ).by_rewrite_of("h_recon_sb", [SYM(p.fact("h_in_sb"))])
                p.have(
                    "h_pre: clear_low s = 0 "
                    "\\/ nat0_lt (low_bit s) (low_bit (clear_low s))"
                ).by(LOW_BIT_CLEAR_LOW_PRECOND, "s", "hnz")
                p.have("h_cl_lt: nat0_lt (clear_low s) s").by(
                    CLEAR_LOW_LT, "s", "hnz"
                )
                p.have("p_cl: P (clear_low s)").by(
                    "IH", "clear_low s", "h_cl_lt"
                )
                p.have(
                    "p_ins: P (Insert (low_bit s) (clear_low s))"
                ).by("step", "low_bit s", "clear_low s", "h_pre", "p_cl")
                p.thus("P s").by_rewrite_of(
                    "p_ins", [SYM(p.fact("h_recon"))]
                )


# ---------------------------------------------------------------------------
# IS_TERM_QUOTE_HF / SUBSTITUTE_QUOTE_HF -- structural facts about the
# image of ``quote_hf``.
#
# ``quote_hf`` produces an HF-syntax encoding using only ``Empty_t`` /
# ``Insert_t`` constructors (no ``Var_t``). Two consequences exploited
# downstream:
#   * IS_TERM_QUOTE_HF: every output is a well-formed HF term.
#   * SUBSTITUTE_QUOTE_HF: substitute on a quote_hf image is identity --
#     no Var_t leaf for the substitution to land on.
#
# Both proofs use STRONG_INDUCTION on ``s`` to access the IH at both
# ``low_bit s`` and ``clear_low s`` (HF_INDUCTION's induction hypothesis
# only fires on the tail, which would force a separate induction on the
# bound head ``i``).
# ---------------------------------------------------------------------------


@proof
def IS_TERM_QUOTE_HF(p):
    """|- !s. is_term (quote_hf s).

    Strong induction on ``s``. Base ``s = 0``: ``quote_hf 0 = Empty_t``
    via EMPTY_DEF + QUOTE_HF_AT_EMPTY; closed by IS_TERM_EMPTY. Step
    ``s != 0``: bit-decompose into ``Insert (low_bit s) (clear_low s)``,
    fire IH at both ``low_bit s`` (LOW_BIT_LT) and ``clear_low s``
    (CLEAR_LOW_LT) under the canonical-form precondition
    LOW_BIT_CLEAR_LOW_PRECOND, then IS_TERM_INSERT closes.
    """
    p.goal("!s. is_term (quote_hf s)")
    with p.strong_induction("s", "IH"):
        with p.cases_on(EXCLUDED_MIDDLE, "s = 0"):
            with p.case("hz: s = 0"):
                p.have("h_eq: quote_hf s = Empty_t").by_rewrite(
                    ["hz", SYM(EMPTY_DEF), QUOTE_HF_AT_EMPTY]
                )
                p.thus("is_term (quote_hf s)").by_rewrite_of(
                    IS_TERM_EMPTY, [SYM(p.fact("h_eq"))]
                )
            with p.case("hnz: ~(s = 0)"):
                p.have("h_lb_lt: nat0_lt (low_bit s) s").by(
                    LOW_BIT_LT, "s", "hnz"
                )
                p.have("h_cl_lt: nat0_lt (clear_low s) s").by(
                    CLEAR_LOW_LT, "s", "hnz"
                )
                p.have(
                    "h_pre: clear_low s = 0 "
                    "\\/ nat0_lt (low_bit s) (low_bit (clear_low s))"
                ).by(LOW_BIT_CLEAR_LOW_PRECOND, "s", "hnz")
                p.have(
                    "h_recon_sb: s = set_bit (low_bit s) (clear_low s)"
                ).by(INSERT_LOW_BIT_CLEAR_LOW, "s", "hnz")
                p.have(
                    "h_in_sb: Insert (low_bit s) (clear_low s) "
                    "= set_bit (low_bit s) (clear_low s)"
                ).by(INSERT_AT, "low_bit s", "clear_low s")
                p.have(
                    "h_recon: s = Insert (low_bit s) (clear_low s)"
                ).by_rewrite_of("h_recon_sb", [SYM(p.fact("h_in_sb"))])
                p.have(
                    "ih_lb: is_term (quote_hf (low_bit s))"
                ).by("IH", "low_bit s", "h_lb_lt")
                p.have(
                    "ih_cl: is_term (quote_hf (clear_low s))"
                ).by("IH", "clear_low s", "h_cl_lt")
                p.have(
                    "h_q_split: quote_hf (Insert (low_bit s) (clear_low s)) "
                    "= Insert_t (quote_hf (low_bit s)) (quote_hf (clear_low s))"
                ).by(
                    QUOTE_HF_AT_INSERT_LOW, "low_bit s", "clear_low s", "h_pre"
                )
                p.have(
                    "h_pair: is_term (quote_hf (low_bit s)) "
                    "/\\ is_term (quote_hf (clear_low s))"
                ).by_thm(CONJ(p.fact("ih_lb"), p.fact("ih_cl")))
                p.have(
                    "h_ins_term: is_term (Insert_t "
                    "(quote_hf (low_bit s)) (quote_hf (clear_low s)))"
                ).by(
                    IS_TERM_INSERT,
                    "quote_hf (low_bit s)",
                    "quote_hf (clear_low s)",
                    "h_pair",
                )
                p.have(
                    "h_q_ins: is_term "
                    "(quote_hf (Insert (low_bit s) (clear_low s)))"
                ).by_rewrite_of("h_ins_term", [SYM(p.fact("h_q_split"))])
                p.thus("is_term (quote_hf s)").by_rewrite_of(
                    "h_q_ins", [SYM(p.fact("h_recon"))]
                )


@proof
def SUBSTITUTE_QUOTE_HF(p):
    """|- !s t v. substitute (quote_hf s) t v = quote_hf s.

    Strong induction on ``s``. Base ``s = 0``: ``quote_hf 0 = Empty_t``
    and SUBSTITUTE_AT_EMPTY closes. Step ``s != 0``: bit-decompose,
    fire IH at both ``low_bit s`` and ``clear_low s``, push substitute
    through Insert_t via SUBSTITUTE_AT_INSERT.

    The ``!t v.`` quantifiers move inside the IH cleanly because both
    are unconstrained -- the IH body holds for any choice.
    """
    p.goal(
        "!s t v. substitute (quote_hf s) t v = quote_hf s",
        types={"s": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    with p.strong_induction("s", "IH"):
        p.fix("t v")
        with p.cases_on(EXCLUDED_MIDDLE, "s = 0"):
            with p.case("hz: s = 0"):
                p.have("h_q_eq: quote_hf s = Empty_t").by_rewrite(
                    ["hz", SYM(EMPTY_DEF), QUOTE_HF_AT_EMPTY]
                )
                p.have(
                    "h_subst_empty: substitute Empty_t t v = Empty_t"
                ).by(SUBSTITUTE_AT_EMPTY, "t", "v")
                p.thus("substitute (quote_hf s) t v = quote_hf s").by_rewrite(
                    ["h_q_eq", "h_subst_empty"]
                )
            with p.case("hnz: ~(s = 0)"):
                p.have("h_lb_lt: nat0_lt (low_bit s) s").by(
                    LOW_BIT_LT, "s", "hnz"
                )
                p.have("h_cl_lt: nat0_lt (clear_low s) s").by(
                    CLEAR_LOW_LT, "s", "hnz"
                )
                p.have(
                    "h_pre: clear_low s = 0 "
                    "\\/ nat0_lt (low_bit s) (low_bit (clear_low s))"
                ).by(LOW_BIT_CLEAR_LOW_PRECOND, "s", "hnz")
                p.have(
                    "h_recon_sb: s = set_bit (low_bit s) (clear_low s)"
                ).by(INSERT_LOW_BIT_CLEAR_LOW, "s", "hnz")
                p.have(
                    "h_in_sb: Insert (low_bit s) (clear_low s) "
                    "= set_bit (low_bit s) (clear_low s)"
                ).by(INSERT_AT, "low_bit s", "clear_low s")
                p.have(
                    "h_recon: s = Insert (low_bit s) (clear_low s)"
                ).by_rewrite_of("h_recon_sb", [SYM(p.fact("h_in_sb"))])
                p.have(
                    "h_q_split: quote_hf (Insert (low_bit s) (clear_low s)) "
                    "= Insert_t (quote_hf (low_bit s)) (quote_hf (clear_low s))"
                ).by(
                    QUOTE_HF_AT_INSERT_LOW, "low_bit s", "clear_low s", "h_pre"
                )
                # AP_TERM quote_hf to h_recon, then TRANS with h_q_split.
                p.have(
                    "h_q_outer: quote_hf s "
                    "= quote_hf (Insert (low_bit s) (clear_low s))"
                ).by_cong("quote_hf", "h_recon")
                p.have(
                    "h_q_eq: quote_hf s "
                    "= Insert_t (quote_hf (low_bit s)) (quote_hf (clear_low s))"
                ).by_thm(TRANS(p.fact("h_q_outer"), p.fact("h_q_split")))
                # IH at low_bit s and clear_low s, specialized at our t, v.
                p.have(
                    "ih_lb_all: !t v. "
                    "substitute (quote_hf (low_bit s)) t v = quote_hf (low_bit s)"
                ).by("IH", "low_bit s", "h_lb_lt")
                p.have(
                    "ih_lb: substitute (quote_hf (low_bit s)) t v "
                    "= quote_hf (low_bit s)"
                ).by("ih_lb_all", "t", "v")
                p.have(
                    "ih_cl_all: !t v. "
                    "substitute (quote_hf (clear_low s)) t v = quote_hf (clear_low s)"
                ).by("IH", "clear_low s", "h_cl_lt")
                p.have(
                    "ih_cl: substitute (quote_hf (clear_low s)) t v "
                    "= quote_hf (clear_low s)"
                ).by("ih_cl_all", "t", "v")
                # Push substitute through Insert_t.
                p.have(
                    "h_subst_ins: substitute (Insert_t "
                    "(quote_hf (low_bit s)) (quote_hf (clear_low s))) t v "
                    "= Insert_t "
                    "(substitute (quote_hf (low_bit s)) t v) "
                    "(substitute (quote_hf (clear_low s)) t v)"
                ).by(
                    SUBSTITUTE_AT_INSERT,
                    "quote_hf (low_bit s)",
                    "quote_hf (clear_low s)",
                    "t",
                    "v",
                )
                p.thus("substitute (quote_hf s) t v = quote_hf s").by_rewrite(
                    ["h_q_eq", "h_subst_ins", "ih_lb", "ih_cl"]
                )


@proof
def IN_INSERT_GROW(p):
    """|- !i s x. In x s ==> In x (Insert i s)."""
    from tactics import EQT_ELIM

    p.goal("!i s x. In x s ==> In x (Insert i s)")
    p.fix("i s x")
    p.assume("hx: In x s")
    with p.cases_on(EXCLUDED_MIDDLE, "i = x"):
        with p.case("hix: i = x"):
            p.have("h_eq: In x (Insert i s) = T").by_rewrite(
                ["hix", IN_INSERT_SAME]
            )
            p.thus("In x (Insert i s)").by_thm(EQT_ELIM(p.fact("h_eq")))
        with p.case("hnix: ~(i = x)"):
            p.have("h_eq: In x (Insert i s) = In x s").by(
                IN_INSERT_DIFF, "i", "x", "s", "hnix"
            )
            p.thus("In x (Insert i s)").by_eq_mp("h_eq", "hx")


@proof
def IN_UNION_LEFT(p):
    """|- !a b x. In x a ==> In x (Union a b)."""
    p.goal("!a b x. In x a ==> In x (Union a b)")
    p.fix("a b x")
    p.assume("hx: In x a")
    p.have("hd: In x a \\/ In x b").by_disj("hx")
    p.have("h_eq: In x (Union a b) = (In x a \\/ In x b)").by(
        IN_UNION, "x", "a", "b"
    )
    p.thus("In x (Union a b)").by_eq_mp("h_eq", "hd")


@proof
def IN_UNION_RIGHT(p):
    """|- !a b x. In x b ==> In x (Union a b)."""
    p.goal("!a b x. In x b ==> In x (Union a b)")
    p.fix("a b x")
    p.assume("hx: In x b")
    p.have("hd: In x a \\/ In x b").by_disj("hx")
    p.have("h_eq: In x (Union a b) = (In x a \\/ In x b)").by(
        IN_UNION, "x", "a", "b"
    )
    p.thus("In x (Union a b)").by_eq_mp("h_eq", "hd")


# ---------------------------------------------------------------------------
# Phase 0/3 prototype for HF-native proof objects.
#
# These lemmas exercise the dependency-set proof-object design before any
# ``Prov_HF_internal`` body is written. They deliberately avoid ``cons_l``
# and list membership. DSL friction is noted inline where the proof needs
# low-level shaping rather than a compact declarative step.
# ---------------------------------------------------------------------------


@proof
def VALID_STEP_HF_SET_PRESERVES(p):
    """|- !P Q k h. (!x. In x P ==> In x Q)
                     ==> valid_step_hf_set P k h
                     ==> valid_step_hf_set Q k h."""
    p.goal(
        "!P Q k h. (!x. In x P ==> In x Q) "
        "==> valid_step_hf_set P k h "
        "==> valid_step_hf_set Q k h",
        types={"P": nat0_ty, "Q": nat0_ty, "k": nat0_ty, "h": nat0_ty},
    )
    p.fix("P Q k h")
    p.assume("sub: !x. In x P ==> In x Q")
    p.assume("vP: valid_step_hf_set P k h")

    atP = SPECL([p._parse("P"), p._parse("k"), p._parse("h")], VALID_STEP_HF_SET_AT)
    atQ = SPECL([p._parse("Q"), p._parse("k"), p._parse("h")], VALID_STEP_HF_SET_AT)
    bodyP = (
        "is_axiom h "
        "\\/ (?i f j g. In (Pair_ord i f) P /\\ In (Pair_ord j g) P "
        "/\\ In i k /\\ In j k /\\ is_mp f g h) "
        "\\/ (?i f. In (Pair_ord i f) P /\\ In i k /\\ is_gen f h)"
    )
    bodyQ = (
        "is_axiom h "
        "\\/ (?i f j g. In (Pair_ord i f) Q /\\ In (Pair_ord j g) Q "
        "/\\ In i k /\\ In j k /\\ is_mp f g h) "
        "\\/ (?i f. In (Pair_ord i f) Q /\\ In i k /\\ is_gen f h)"
    )
    p.have(f"bodyP: {bodyP}").by_eq_mp(atP, "vP")
    with p.cases_on("bodyP"):
        with p.case("ax: is_axiom h"):
            p.have(f"bodyQ: {bodyQ}").by_disj("ax")
            p.thus("valid_step_hf_set Q k h").by_eq_mp(SYM(atQ), "bodyQ")
        with p.case(
            "mpP: ?i f j g. In (Pair_ord i f) P /\\ In (Pair_ord j g) P "
            "/\\ In i k /\\ In j k /\\ is_mp f g h"
        ):
            p.split("g_eq", "(in_i_P, in_j_P, in_i_dep, in_j_dep, mp)")
            p.have("in_i_Q: In (Pair_ord i f) Q").by("sub", "Pair_ord i f", "in_i_P")
            p.have("in_j_Q: In (Pair_ord j g) Q").by("sub", "Pair_ord j g", "in_j_P")
            # DSL friction: by_exists wants each substituted conjunct as
            # a separate rule; passing a prebuilt conjunction is rejected.
            p.have(
                "mpQ: ?i f j g. In (Pair_ord i f) Q /\\ In (Pair_ord j g) Q "
                "/\\ In i k /\\ In j k /\\ is_mp f g h"
            ).by_exists(
                ["i", "f", "j", "g"],
                "in_i_Q",
                "in_j_Q",
                "in_i_dep",
                "in_j_dep",
                "mp",
            )
            p.have(f"bodyQ: {bodyQ}").by_disj("mpQ")
            p.thus("valid_step_hf_set Q k h").by_eq_mp(SYM(atQ), "bodyQ")
        with p.case("genP: ?i f. In (Pair_ord i f) P /\\ In i k /\\ is_gen f h"):
            p.split("f_eq", "(in_i_P, in_i_dep, gen)")
            p.have("in_i_Q: In (Pair_ord i f) Q").by("sub", "Pair_ord i f", "in_i_P")
            p.have("genQ: ?i f. In (Pair_ord i f) Q /\\ In i k /\\ is_gen f h").by_exists(
                ["i", "f"], "in_i_Q", "in_i_dep", "gen"
            )
            p.have(f"bodyQ: {bodyQ}").by_disj("genQ")
            p.thus("valid_step_hf_set Q k h").by_eq_mp(SYM(atQ), "bodyQ")


@proof
def AXIOM_HAS_PROOF_HF_SET(p):
    """|- !m. is_axiom m ==> ?P. Proof_HF_set P m."""
    from tactics import EQT_ELIM

    p.goal("!m. is_axiom m ==> ?P. Proof_HF_set P m")
    p.fix("m")
    p.assume("ax: is_axiom m")

    P = "Insert (Pair_ord Empty m) Empty"
    p.have(f"in_head_eq: In (Pair_ord Empty m) ({P}) = T").by_rewrite([IN_INSERT_SAME])
    p.have(f"in_head: In (Pair_ord Empty m) ({P})").by_thm(
        EQT_ELIM(p.fact("in_head_eq"))
    )

    with p.have(
        f"valid_all: !j h. In (Pair_ord j h) ({P}) ==> valid_step_hf_set ({P}) j h"
    ).proof():
        p.fix("j h")
        p.assume(f"hin: In (Pair_ord j h) ({P})")
        with p.cases_on(EXCLUDED_MIDDLE, "Pair_ord Empty m = Pair_ord j h"):
            with p.case("heq: Pair_ord Empty m = Pair_ord j h"):
                p.have("inj: Empty = j /\\ m = h").by(
                    PAIR_ORD_INJ, "Empty", "m", "j", "h", "heq"
                )
                p.split("inj", "(_j_eq, m_eq_h)")
                p.have("ax_h: is_axiom h").by_rewrite_of("ax", ["m_eq_h"])
                atP = SPECL([p._parse(P), p._parse("j"), p._parse("h")], VALID_STEP_HF_SET_AT)
                body = (
                    f"is_axiom h \\/ (?i f j0 g. In (Pair_ord i f) ({P}) "
                    f"/\\ In (Pair_ord j0 g) ({P}) /\\ In i j "
                    f"/\\ In j0 j /\\ is_mp f g h) "
                    f"\\/ (?i f. In (Pair_ord i f) ({P}) /\\ In i j /\\ is_gen f h)"
                )
                p.have(f"vbody: {body}").by_disj("ax_h")
                p.thus(f"valid_step_hf_set ({P}) j h").by_eq_mp(SYM(atP), "vbody")
            with p.case("hne: ~(Pair_ord Empty m = Pair_ord j h)"):
                p.have(f"hin_empty_eq: In (Pair_ord j h) ({P}) = In (Pair_ord j h) Empty").by(
                    IN_INSERT_DIFF, "Pair_ord Empty m", "Pair_ord j h", "Empty", "hne"
                )
                p.have("hin_empty: In (Pair_ord j h) Empty").by_eq_mp("hin_empty_eq", "hin")
                p.have("not_empty: ~In (Pair_ord j h) Empty").by(
                    NOT_IN_EMPTY, "Pair_ord j h"
                )
                # DSL friction: there is no direct "ex falso" have-step
                # for an arbitrary target. Build the F theorem explicitly
                # and feed it through CONTR.
                F_th = MP(NOT_ELIM(p.fact("not_empty")), p.fact("hin_empty"))
                target = p._parse(f"valid_step_hf_set ({P}) j h")
                p.thus(f"valid_step_hf_set ({P}) j h").by_thm(CONTR(target, F_th))

    proof_at = SPECL([p._parse(P), p._parse("m")], PROOF_HF_SET_AT)
    p.have(
        f"body: ?k. In (Pair_ord k m) ({P}) "
        f"/\\ (!j h. In (Pair_ord j h) ({P}) ==> valid_step_hf_set ({P}) j h)"
    ).by_exists(["Empty"], "in_head", "valid_all")
    p.have(f"proof_set: Proof_HF_set ({P}) m").by_eq_mp(SYM(proof_at), "body")
    p.thus("?P. Proof_HF_set P m").by_witness(P, "proof_set")


@proof
def MP_HAS_PROOF_HF_SET(p):
    """|- !f g. (?P. Proof_HF_set P f)
              /\\ (?Q. Proof_HF_set Q (Imp_f f g))
              ==> ?R. Proof_HF_set R g."""
    from tactics import EQT_ELIM

    p.goal(
        "!f g. (?P. Proof_HF_set P f) /\\ (?Q. Proof_HF_set Q (Imp_f f g)) "
        "==> ?R. Proof_HF_set R g"
    )
    p.fix("f g")
    p.assume("(pf_ex, pfg_ex): (?P. Proof_HF_set P f) /\\ (?Q. Proof_HF_set Q (Imp_f f g))")
    p.choose("P", "pf_ex", eq_label="pf")
    p.choose("Q", "pfg_ex", eq_label="pfg")

    atP = SPECL([p._parse("P"), p._parse("f")], PROOF_HF_SET_AT)
    atQ = SPECL([p._parse("Q"), p._parse("Imp_f f g")], PROOF_HF_SET_AT)
    p.have(
        "bodyP: ?k. In (Pair_ord k f) P "
        "/\\ (!j h. In (Pair_ord j h) P ==> valid_step_hf_set P j h)"
    ).by_eq_mp(atP, "pf")
    p.have(
        "bodyQ: ?k. In (Pair_ord k (Imp_f f g)) Q "
        "/\\ (!j h. In (Pair_ord j h) Q ==> valid_step_hf_set Q j h)"
    ).by_eq_mp(atQ, "pfg")
    p.choose("kf", "bodyP", eq_label="pf_body")
    p.split("pf_body", "(in_f_P, validP)")
    p.choose("kg", "bodyQ", eq_label="pfg_body")
    p.split("pfg_body", "(in_imp_Q, validQ)")

    R = "Insert (Pair_ord (Pair kf kg) g) (Union P Q)"
    kR = "Pair kf kg"

    with p.have(f"subP: !x. In x P ==> In x ({R})").proof():
        p.fix("x")
        p.assume("hx: In x P")
        p.have("h_union: In x (Union P Q)").by(IN_UNION_LEFT, "P", "Q", "x", "hx")
        p.thus(f"In x ({R})").by(IN_INSERT_GROW, f"Pair_ord ({kR}) g", "Union P Q", "x", "h_union")

    with p.have(f"subQ: !x. In x Q ==> In x ({R})").proof():
        p.fix("x")
        p.assume("hx: In x Q")
        p.have("h_union: In x (Union P Q)").by(IN_UNION_RIGHT, "P", "Q", "x", "hx")
        p.thus(f"In x ({R})").by(IN_INSERT_GROW, f"Pair_ord ({kR}) g", "Union P Q", "x", "h_union")

    p.have(f"in_f_R: In (Pair_ord kf f) ({R})").by("subP", "Pair_ord kf f", "in_f_P")
    p.have(f"in_imp_R: In (Pair_ord kg (Imp_f f g)) ({R})").by(
        "subQ", "Pair_ord kg (Imp_f f g)", "in_imp_Q"
    )
    p.have(f"in_g_R_eq: In (Pair_ord ({kR}) g) ({R}) = T").by_rewrite([IN_INSERT_SAME])
    p.have(f"in_g_R: In (Pair_ord ({kR}) g) ({R})").by_thm(EQT_ELIM(p.fact("in_g_R_eq")))

    with p.have(
        f"valid_all: !j h. In (Pair_ord j h) ({R}) ==> valid_step_hf_set ({R}) j h"
    ).proof():
        p.fix("j h")
        p.assume(f"hin: In (Pair_ord j h) ({R})")
        with p.cases_on(EXCLUDED_MIDDLE, f"Pair_ord ({kR}) g = Pair_ord j h"):
            with p.case(f"heq: Pair_ord ({kR}) g = Pair_ord j h"):
                p.have(f"inj: ({kR}) = j /\\ g = h").by(
                    PAIR_ORD_INJ, kR, "g", "j", "h", "heq"
                )
                p.split("inj", "(rank_eq, g_eq_h)")
                p.have("kf_refl: kf = kf").by_thm(REFL(p._parse("kf")))
                p.have("kf_disj: kf = kf \\/ kf = kg").by_disj("kf_refl")
                p.have("in_kf_eq: In kf (Pair kf kg) = (kf = kf \\/ kf = kg)").by(
                    IN_PAIR, "kf", "kg", "kf"
                )
                p.have("in_kf_rank: In kf (Pair kf kg)").by_eq_mp(
                    SYM(p.fact("in_kf_eq")), "kf_disj"
                )
                p.have("kg_refl: kg = kg").by_thm(REFL(p._parse("kg")))
                p.have("kg_disj: kg = kf \\/ kg = kg").by_disj("kg_refl")
                p.have("in_kg_eq: In kg (Pair kf kg) = (kg = kf \\/ kg = kg)").by(
                    IN_PAIR, "kf", "kg", "kg"
                )
                p.have("in_kg_rank: In kg (Pair kf kg)").by_eq_mp(
                    SYM(p.fact("in_kg_eq")), "kg_disj"
                )
                p.have("in_kf_j: In kf j").by_rewrite_of("in_kf_rank", ["rank_eq"])
                p.have("in_kg_j: In kg j").by_rewrite_of("in_kg_rank", ["rank_eq"])
                is_mp_at = SPECL(
                    [p._parse("f"), p._parse("Imp_f f g"), p._parse("g")],
                    IS_MP_AT,
                )
                p.have("mp_g: is_mp f (Imp_f f g) g").by_eq_mp(
                    SYM(is_mp_at), REFL(p._parse("Imp_f f g"))
                )
                p.have("mp_h: is_mp f (Imp_f f g) h").by_rewrite_of("mp_g", ["g_eq_h"])
                p.have(
                    f"mp_ex: ?i f0 j0 g0. In (Pair_ord i f0) ({R}) "
                    f"/\\ In (Pair_ord j0 g0) ({R}) /\\ In i j "
                    f"/\\ In j0 j /\\ is_mp f0 g0 h"
                ).by_exists(
                    ["kf", "f", "kg", "Imp_f f g"],
                    "in_f_R",
                    "in_imp_R",
                    "in_kf_j",
                    "in_kg_j",
                    "mp_h",
                )
                atR = SPECL([p._parse(R), p._parse("j"), p._parse("h")], VALID_STEP_HF_SET_AT)
                body = (
                    f"is_axiom h \\/ (?i f0 j0 g0. In (Pair_ord i f0) ({R}) "
                    f"/\\ In (Pair_ord j0 g0) ({R}) /\\ In i j "
                    f"/\\ In j0 j /\\ is_mp f0 g0 h) "
                    f"\\/ (?i f0. In (Pair_ord i f0) ({R}) /\\ In i j /\\ is_gen f0 h)"
                )
                p.have(f"vbody: {body}").by_disj("mp_ex")
                p.thus(f"valid_step_hf_set ({R}) j h").by_eq_mp(SYM(atR), "vbody")
            with p.case(f"hne: ~(Pair_ord ({kR}) g = Pair_ord j h)"):
                p.have(f"hin_union_eq: In (Pair_ord j h) ({R}) = In (Pair_ord j h) (Union P Q)").by(
                    IN_INSERT_DIFF, f"Pair_ord ({kR}) g", "Pair_ord j h", "Union P Q", "hne"
                )
                p.have("hin_union: In (Pair_ord j h) (Union P Q)").by_eq_mp(
                    "hin_union_eq", "hin"
                )
                p.have(
                    "hin_disj: In (Pair_ord j h) P \\/ In (Pair_ord j h) Q"
                ).by_eq_mp(
                    SYM(SPECL([p._parse("Pair_ord j h"), p._parse("P"), p._parse("Q")], IN_UNION)),
                    "hin_union",
                )
                with p.cases_on("hin_disj"):
                    with p.case("hinP: In (Pair_ord j h) P"):
                        p.have("vP: valid_step_hf_set P j h").by("validP", "j", "h", "hinP")
                        p.thus(f"valid_step_hf_set ({R}) j h").by(
                            VALID_STEP_HF_SET_PRESERVES, "P", R, "j", "h", "subP", "vP"
                        )
                    with p.case("hinQ: In (Pair_ord j h) Q"):
                        p.have("vQ: valid_step_hf_set Q j h").by("validQ", "j", "h", "hinQ")
                        p.thus(f"valid_step_hf_set ({R}) j h").by(
                            VALID_STEP_HF_SET_PRESERVES, "Q", R, "j", "h", "subQ", "vQ"
                        )

    proof_at = SPECL([p._parse(R), p._parse("g")], PROOF_HF_SET_AT)
    p.have(
        f"body: ?k. In (Pair_ord k g) ({R}) "
        f"/\\ (!j h. In (Pair_ord j h) ({R}) ==> valid_step_hf_set ({R}) j h)"
    ).by_exists([kR], "in_g_R", "valid_all")
    p.have(f"proof_R: Proof_HF_set ({R}) g").by_eq_mp(SYM(proof_at), "body")
    p.thus("?R. Proof_HF_set R g").by_witness(R, "proof_R")


@proof
def GEN_HAS_PROOF_HF_SET(p):
    """|- !f x. (?P. Proof_HF_set P f)
              ==> ?R. Proof_HF_set R (Forall_f x f)."""
    from tactics import EQT_ELIM

    p.goal("!f x. (?P. Proof_HF_set P f) ==> ?R. Proof_HF_set R (Forall_f x f)")
    p.fix("f x")
    p.assume("pf_ex: ?P. Proof_HF_set P f")
    p.choose("P", "pf_ex", eq_label="pf")

    atP = SPECL([p._parse("P"), p._parse("f")], PROOF_HF_SET_AT)
    p.have(
        "bodyP: ?k. In (Pair_ord k f) P "
        "/\\ (!j h. In (Pair_ord j h) P ==> valid_step_hf_set P j h)"
    ).by_eq_mp(atP, "pf")
    p.choose("kf", "bodyP", eq_label="pf_body")
    p.split("pf_body", "(in_f_P, validP)")

    R = "Insert (Pair_ord (Singleton kf) (Forall_f x f)) P"
    kR = "Singleton kf"

    with p.have(f"subP: !z. In z P ==> In z ({R})").proof():
        p.fix("z")
        p.assume("hz: In z P")
        p.thus(f"In z ({R})").by(
            IN_INSERT_GROW, f"Pair_ord ({kR}) (Forall_f x f)", "P", "z", "hz"
        )

    p.have(f"in_f_R: In (Pair_ord kf f) ({R})").by("subP", "Pair_ord kf f", "in_f_P")
    p.have(f"in_gen_R_eq: In (Pair_ord ({kR}) (Forall_f x f)) ({R}) = T").by_rewrite(
        [IN_INSERT_SAME]
    )
    # DSL friction: rewriting set membership gives an equation to T;
    # convert it to the boolean fact before using it as a conjunct.
    p.have(f"in_gen_R: In (Pair_ord ({kR}) (Forall_f x f)) ({R})").by_thm(
        EQT_ELIM(p.fact("in_gen_R_eq"))
    )

    is_gen_at = SPECL([p._parse("f"), p._parse("Forall_f x f")], IS_GEN_AT)
    p.have("gen_witness: ?y. Forall_f x f = Forall_f y f").by_witness(
        "x", REFL(p._parse("Forall_f x f"))
    )
    p.have("gen_fx: is_gen f (Forall_f x f)").by_eq_mp(SYM(is_gen_at), "gen_witness")

    with p.have(
        f"valid_all: !j h. In (Pair_ord j h) ({R}) ==> valid_step_hf_set ({R}) j h"
    ).proof():
        p.fix("j h")
        p.assume(f"hin: In (Pair_ord j h) ({R})")
        with p.cases_on(EXCLUDED_MIDDLE, f"Pair_ord ({kR}) (Forall_f x f) = Pair_ord j h"):
            with p.case(f"heq: Pair_ord ({kR}) (Forall_f x f) = Pair_ord j h"):
                p.have(f"inj: ({kR}) = j /\\ Forall_f x f = h").by(
                    PAIR_ORD_INJ, kR, "Forall_f x f", "j", "h", "heq"
                )
                p.split("inj", "(rank_eq, forall_eq_h)")
                p.have("kf_refl: kf = kf").by_thm(REFL(p._parse("kf")))
                p.have("in_kf_eq: In kf (Singleton kf) = (kf = kf)").by(
                    IN_SINGLETON, "kf", "kf"
                )
                p.have("in_kf_rank: In kf (Singleton kf)").by_eq_mp(
                    SYM(p.fact("in_kf_eq")), "kf_refl"
                )
                p.have("in_kf_j: In kf j").by_rewrite_of("in_kf_rank", ["rank_eq"])
                p.have("gen_h: is_gen f h").by_rewrite_of("gen_fx", ["forall_eq_h"])
                p.have(
                    f"gen_ex: ?i f0. In (Pair_ord i f0) ({R}) "
                    f"/\\ In i j /\\ is_gen f0 h"
                ).by_exists(["kf", "f"], "in_f_R", "in_kf_j", "gen_h")
                atR = SPECL([p._parse(R), p._parse("j"), p._parse("h")], VALID_STEP_HF_SET_AT)
                body = (
                    f"is_axiom h \\/ (?i f0 j0 g0. In (Pair_ord i f0) ({R}) "
                    f"/\\ In (Pair_ord j0 g0) ({R}) /\\ In i j "
                    f"/\\ In j0 j /\\ is_mp f0 g0 h) "
                    f"\\/ (?i f0. In (Pair_ord i f0) ({R}) /\\ In i j /\\ is_gen f0 h)"
                )
                p.have(f"vbody: {body}").by_disj("gen_ex")
                p.thus(f"valid_step_hf_set ({R}) j h").by_eq_mp(SYM(atR), "vbody")
            with p.case(f"hne: ~(Pair_ord ({kR}) (Forall_f x f) = Pair_ord j h)"):
                p.have(f"hin_P_eq: In (Pair_ord j h) ({R}) = In (Pair_ord j h) P").by(
                    IN_INSERT_DIFF,
                    f"Pair_ord ({kR}) (Forall_f x f)",
                    "Pair_ord j h",
                    "P",
                    "hne",
                )
                p.have("hinP: In (Pair_ord j h) P").by_eq_mp("hin_P_eq", "hin")
                p.have("vP: valid_step_hf_set P j h").by("validP", "j", "h", "hinP")
                p.thus(f"valid_step_hf_set ({R}) j h").by(
                    VALID_STEP_HF_SET_PRESERVES, "P", R, "j", "h", "subP", "vP"
                )

    proof_at = SPECL([p._parse(R), p._parse("Forall_f x f")], PROOF_HF_SET_AT)
    p.have(
        f"body: ?k. In (Pair_ord k (Forall_f x f)) ({R}) "
        f"/\\ (!j h. In (Pair_ord j h) ({R}) ==> valid_step_hf_set ({R}) j h)"
    ).by_exists([kR], "in_gen_R", "valid_all")
    p.have(f"proof_R: Proof_HF_set ({R}) (Forall_f x f)").by_eq_mp(SYM(proof_at), "body")
    p.thus("?R. Proof_HF_set R (Forall_f x f)").by_witness(R, "proof_R")



# ---------------------------------------------------------------------------
# Stage 3B (k) -- set-native closure rules.
#
#   (1) |- !n. is_axiom n ==> Prov_HF n.
#   (2) |- !f g. Prov_HF f /\ Prov_HF (Imp_f f g) ==> Prov_HF g.
#   (3) |- !f x. Prov_HF f ==> Prov_HF (Forall_f x f).
#
# Each closure rule packages the corresponding HF-set proof-object
# prototype through ``PROV_HF_AT``.
# ---------------------------------------------------------------------------


@proof
def PROV_HF_AXIOM(p):
    """|- !n. is_axiom n ==> Prov_HF n."""
    p.goal("!n. is_axiom n ==> Prov_HF n")
    p.fix("n")
    p.assume("ax: is_axiom n")
    p.have("ex: ?P. Proof_HF_set P n").by(AXIOM_HAS_PROOF_HF_SET, "n", "ax")
    pq_at_n = SPEC(p._parse("n"), PROV_HF_AT)
    p.thus("Prov_HF n").by_eq_mp(SYM(pq_at_n), "ex")


@proof
def PROV_HF_MP(p):
    r"""|- !f g. Prov_HF f /\ Prov_HF (Imp_f f g) ==> Prov_HF g."""
    p.goal("!f g. (Prov_HF f /\\ Prov_HF (Imp_f f g)) ==> Prov_HF g")
    p.fix("f g")
    p.assume("(pf, pfg): Prov_HF f /\\ Prov_HF (Imp_f f g)")
    pq_at_f = SPEC(p._parse("f"), PROV_HF_AT)
    pq_at_fg = SPEC(p._parse("Imp_f f g"), PROV_HF_AT)
    pq_at_g = SPEC(p._parse("g"), PROV_HF_AT)
    p.have("ex_f: ?P. Proof_HF_set P f").by_eq_mp(pq_at_f, "pf")
    p.have("ex_fg: ?Q. Proof_HF_set Q (Imp_f f g)").by_eq_mp(pq_at_fg, "pfg")
    p.have("ex_g: ?R. Proof_HF_set R g").by(
        MP_HAS_PROOF_HF_SET, "f", "g", CONJ(p.fact("ex_f"), p.fact("ex_fg"))
    )
    p.thus("Prov_HF g").by_eq_mp(SYM(pq_at_g), "ex_g")


@proof
def PROV_HF_GEN(p):
    """|- !f x. Prov_HF f ==> Prov_HF (Forall_f x f)."""
    p.goal("!f x. Prov_HF f ==> Prov_HF (Forall_f x f)")
    p.fix("f x")
    p.assume("pf: Prov_HF f")
    pq_at_f = SPEC(p._parse("f"), PROV_HF_AT)
    pq_at_fx = SPEC(p._parse("Forall_f x f"), PROV_HF_AT)
    p.have("ex_f: ?P. Proof_HF_set P f").by_eq_mp(pq_at_f, "pf")
    p.have("ex_fx: ?R. Proof_HF_set R (Forall_f x f)").by(
        GEN_HAS_PROOF_HF_SET, "f", "x", "ex_f"
    )
    p.thus("Prov_HF (Forall_f x f)").by_eq_mp(SYM(pq_at_fx), "ex_fx")


# ``Prov_HF`` is defined directly from set-native proof objects.
PROV_HF_IFF_PROOF_HF_SET = PROV_HF_AT


# Helper: lift |- is_<X> n through the logical-axiom disjunction chain
# to |- Prov_HF n. Mirrors hf_logic._prov_of_logical (which sits a layer
# above and cannot be imported here without a cycle); duplicated locally
# so Stage 3 representability proofs can witness the Refl/Subst schemas
# without taking a dep on hf_logic.
#
# slot_idx: position in IS_LOGICAL_AXIOM_AT's right-associated 7-way OR.
#   0=K, 1=S, 2=N, 3=UI, 4=Vac, 5=Refl, 6=Subst.
def _prov_of_logical_lift(slot_th, slot_idx, n_term):
    is_logical_at = SPEC(n_term, IS_LOGICAL_AXIOM_AT)
    rhs_disj = rand(is_logical_at._concl)
    # Walk rhs_disj as a right-associated disjunction; collect parts.
    from fusion import Const

    parts = []
    cur = rhs_disj
    while True:
        try:
            outer = rator(cur)
            head = rator(outer)
            if isinstance(head, Const) and head.name == "\\/":
                parts.append(rand(outer))
                cur = rand(cur)
                continue
        except Exception:
            pass
        parts.append(cur)
        break
    th = slot_th
    if slot_idx < len(parts) - 1:
        suffix = rhs_disj
        for _ in range(slot_idx):
            suffix = rand(suffix)
        th = DISJ1(th, rand(suffix))
    for k in range(slot_idx - 1, -1, -1):
        th = DISJ2(parts[k], th)
    is_logical_th = EQ_MP(SYM(is_logical_at), th)
    is_axiom_at = SPEC(n_term, IS_AXIOM_AT)
    q_hf_part = mk_app(is_hf_axiom, n_term)
    ind_part = mk_app(is_hf_ind_axiom, n_term)
    ind_or_logical_th = DISJ2(ind_part, is_logical_th)
    is_axiom_th = EQ_MP(SYM(is_axiom_at), DISJ2(q_hf_part, ind_or_logical_th))
    prov_at_n = SPEC(n_term, PROV_HF_AXIOM)
    return MP(prov_at_n, is_axiom_th)


@proof
def PROV_HF_REFL(p):
    """|- !t. is_term t ==> Prov_HF (Eq_f t t).

    Reflexivity-of-equality logical-axiom schema (slot 5: is_Refl).
    Witnesses ``?t1. is_term t1 /\\ Eq_f t t = Eq_f t1 t1`` at ``t1 := t``,
    then lifts is_Refl -> is_logical_axiom -> is_axiom -> Prov_HF.
    """
    p.goal(
        "!t. is_term t ==> Prov_HF (Eq_f t t)",
        types={"t": nat0_ty},
    )
    p.fix("t")
    p.assume("ht: is_term t")
    n_term = p._parse("Eq_f t t")
    is_refl_at_n = SPEC(n_term, IS_REFL_AT)
    p.have(
        "rbody: ?t1. is_term t1 /\\ Eq_f t t = Eq_f t1 t1"
    ).by_exists(["t"], "ht")
    is_refl_th = EQ_MP(SYM(is_refl_at_n), p.fact("rbody"))
    p.thus("Prov_HF (Eq_f t t)").by_thm(
        _prov_of_logical_lift(is_refl_th, 5, n_term)
    )


# B1.0 (b) -- Pair_ord representability.
# Needed by HF-set proof objects and by quoted Kuratowski-pair bridges:
# HF must prove the encoded pair shape at concrete numerals.
#
# Body: faithful equational encoding of the Kuratowski pair shape --
# ``var_z = {{var_x}, {var_x, var_y}}``.  The quoted-data RHS is built
# through ``qparse`` rather than by spelling the ``Insert_t`` tower out
# directly, which exercises the quoted-template notation used by later
# internal bodies.
#
#   Eq_f var_z
#     (Insert_t (Insert_t var_x Empty_t)        -- {var_x}
#       (Insert_t                                -- + {{var_x, var_y}}
#         (Insert_t var_x (Insert_t var_y Empty_t))   -- = {var_x, var_y}
#         Empty_t))
#
# This matches QUOTE_HF_AT_PAIR_ORD's RHS shape; substituting the three
# slots with ``quote_hf x``, ``quote_hf y``, ``quote_hf (Pair_ord x y)``
# yields a reflexivity claim that PROV_HF_REFL closes -- but the bridge
# requires ``nat0_lt x y`` (QUOTE_HF_AT_PAIR_ORD's precondition). The
# theorem ``IS_PAIR_ORD_REPRESENTS`` carries the precondition
# explicitly; downstream consumers instantiate it at concrete numerals
# where the order is easily established.
_PAIR_ORD_TEMPLATE = qparse("Pair_ord(var_x,var_y)", var_x=var_x, var_y=var_y)


IS_PAIR_ORD_INTERNAL_DEF = define(
    "is_Pair_ord_internal",
    nat0_ty,
    mk_app(mk_app(Eq_f, var_z), _PAIR_ORD_TEMPLATE),
)
is_Pair_ord_internal = mk_const("is_Pair_ord_internal", [])


# Six unconditional substitute lemmas covering the (var_X, idx_Y) pairs
# encountered while walking the threefold substitute over
# is_Pair_ord_internal:
#   HIT:   substitute var_X t idx_X = t  (X in {x, y, z})
#   MISS:  substitute var_X t idx_Y = var_X  (X != Y)
# Built by SPECL'ing SUBSTITUTE_AT_VAR_HIT/MISS at the concrete indices
# (0, SUC0 0, SUC0 SUC0 0), discharging the precondition (REFL for HIT,
# AXIOM_3_0/AXIOM_4_0 for MISS), and folding back via VAR_*_DEF and
# IDX_*_DEF. They function as the "leaf-rewrite" rules feeding the by-
# rewrite that collapses the threefold substitute below.
_t_subst = Var("t", nat0_ty)


def _build_hit(var_def, idx_def, inner_idx):
    """|- !t. substitute var_X t idx_X = t.

    Two-stage fold: first apply ``SYM(var_def)`` to collapse the
    ``Var_t inner_idx`` pattern into the named constant ``var_X``,
    then apply ``SYM(idx_def)`` to fold the remaining substitute-
    parameter occurrence ``inner_idx`` into ``idx_X``. Applying both
    rules in one pass would let the deep-first rewriter rewrite the
    inner ``inner_idx`` of ``Var_t inner_idx`` first, blocking the
    var-fold.
    """
    base = MP(
        SPECL([inner_idx, _t_subst, inner_idx], SUBSTITUTE_AT_VAR_HIT),
        REFL(inner_idx),
    )
    folded = REWRITE_RULE([SYM(var_def)], base)
    folded = REWRITE_RULE([SYM(idx_def)], folded)
    return GEN(_t_subst, folded)


def _build_miss(var_def, idx_def, inner_idx, idx_val, neq_th):
    """|- !t. substitute var_X t idx_Y = var_X (X != Y)."""
    base = MP(
        SPECL([inner_idx, _t_subst, idx_val], SUBSTITUTE_AT_VAR_MISS),
        neq_th,
    )
    folded = REWRITE_RULE([SYM(var_def)], base)
    folded = REWRITE_RULE([SYM(idx_def)], folded)
    return GEN(_t_subst, folded)


# ~(SUC0 0 = 0) and the six index-inequalities derived from AXIOM_3_0 +
# AXIOM_4_0. Each takes one or two lines.
_neq_s0_0 = SPEC(ZERO, AXIOM_3_0)              # ~(SUC0 0 = 0)
_neq_ss0_0 = SPEC(mk_suc0(ZERO), AXIOM_3_0)    # ~(SUC0 (SUC0 0) = 0)


def _flip_neq(neq_th, lhs_term, rhs_term):
    """From ``|- ~(a = b)`` derive ``|- ~(b = a)``."""
    asm = ASSUME(mk_eq(rhs_term, lhs_term))    # b = a |- b = a
    a_eq_b = SYM(asm)                           # b = a |- a = b
    contra = MP(NOT_ELIM(neq_th), a_eq_b)       # b = a |- F
    return NOT_INTRO(DISCH(mk_eq(rhs_term, lhs_term), contra))


_neq_0_s0 = _flip_neq(_neq_s0_0, mk_suc0(ZERO), ZERO)        # ~(0 = SUC0 0)
_neq_0_ss0 = _flip_neq(
    _neq_ss0_0, mk_suc0(mk_suc0(ZERO)), ZERO
)  # ~(0 = SUC0 (SUC0 0))

# ~(SUC0 0 = SUC0 (SUC0 0)) via AXIOM_4_0 contrapositive on ~(0 = SUC0 0).
def _build_neq_s0_ss0():
    # AXIOM_4_0: !m n. SUC0 m = SUC0 n ==> m = n.
    # Specialize m=0, n=SUC0 0: SUC0 0 = SUC0 (SUC0 0) ==> 0 = SUC0 0.
    inj = SPECL([ZERO, mk_suc0(ZERO)], AXIOM_4_0)
    asm = ASSUME(mk_eq(mk_suc0(ZERO), mk_suc0(mk_suc0(ZERO))))
    z_eq_s0 = MP(inj, asm)
    contra = MP(NOT_ELIM(_neq_0_s0), z_eq_s0)
    return NOT_INTRO(
        DISCH(mk_eq(mk_suc0(ZERO), mk_suc0(mk_suc0(ZERO))), contra)
    )


_neq_s0_ss0 = _build_neq_s0_ss0()
# ~(SUC0 (SUC0 0) = SUC0 0) is the symmetric counterpart -- flip
# ~(SUC0 0 = SUC0 (SUC0 0)) so the lhs/rhs args match the original eq.
_neq_ss0_s0 = _flip_neq(
    _neq_s0_ss0, mk_suc0(ZERO), mk_suc0(mk_suc0(ZERO))
)

# Build the six leaf-rewrite lemmas.
_SUBST_VX_AT_X = _build_hit(VAR_X_DEF, IDX_X_DEF, ZERO)
_SUBST_VY_AT_Y = _build_hit(VAR_Y_DEF, IDX_Y_DEF, mk_suc0(ZERO))
_SUBST_VZ_AT_Z = _build_hit(VAR_Z_DEF, IDX_Z_DEF, mk_suc0(mk_suc0(ZERO)))
# MISS: substitute var_y t idx_x = var_y. var_y inner = SUC0 0; v = 0.
# cond ~(0 = SUC0 0) = _neq_0_s0.
_SUBST_VY_AT_X = _build_miss(
    VAR_Y_DEF, IDX_X_DEF, mk_suc0(ZERO), ZERO, _neq_0_s0
)
# MISS: substitute var_z t idx_x = var_z. var_z inner = SUC0 SUC0 0; v = 0.
_SUBST_VZ_AT_X = _build_miss(
    VAR_Z_DEF, IDX_X_DEF, mk_suc0(mk_suc0(ZERO)), ZERO, _neq_0_ss0
)
# MISS: substitute var_z t idx_y = var_z. var_z inner = SUC0 SUC0 0; v = SUC0 0.
_SUBST_VZ_AT_Y = _build_miss(
    VAR_Z_DEF,
    IDX_Y_DEF,
    mk_suc0(mk_suc0(ZERO)),
    mk_suc0(ZERO),
    _neq_s0_ss0,
)


@proof
def IS_PAIR_ORD_REPRESENTS(p):
    """|- !x y. nat0_lt x y ==>
                Prov_HF (substitute^3 is_Pair_ord_internal
                          (quote_hf x) idx_x
                          (quote_hf y) idx_y
                          (quote_hf (Pair_ord x y)) idx_z).

    Faithful encoding: with
    ``is_Pair_ord_internal := Eq_f var_z (<Insert_t tower over var_x,
    var_y, Empty_t>)`` (the syntactic Kuratowski pair shape), the
    threefold substitute walks each layer via SUBSTITUTE_AT_EQ /
    SUBSTITUTE_AT_INSERT / SUBSTITUTE_AT_EMPTY, replaces the var_x /
    var_y / var_z leaves with quote_hf x / quote_hf y / quote_hf
    (Pair_ord x y) via the six leaf lemmas built above, and treats
    quote_hf'd subterms as closed via SUBSTITUTE_QUOTE_HF.

    The fully substituted form is ``Eq_f (quote_hf (Pair_ord x y))
    <Insert tower>``; QUOTE_HF_AT_PAIR_ORD (under ``nat0_lt x y``)
    rewrites the LHS into the same Insert tower, so PROV_HF_REFL closes
    via IS_TERM_QUOTE_HF + IS_TERM_INSERT + IS_TERM_EMPTY.
    """
    p.goal(
        "!x y. nat0_lt x y ==> "
        "Prov_HF (substitute (substitute (substitute "
        "  is_Pair_ord_internal (quote_hf x) idx_x) "
        "  (quote_hf y) idx_y) "
        "  (quote_hf (Pair_ord x y)) idx_z)"
    )
    p.fix("x y")
    p.assume("hxy: nat0_lt x y")

    # Compute the threefold substitute symbolically. The leaf lemmas
    # _SUBST_V*_AT_* push substitute past the var_x/y/z leaves; the
    # AT-equations push through Eq_f / Insert_t / Empty_t; quoted
    # subterms (quote_hf x, quote_hf y) are unchanged by SUBSTITUTE_QUOTE_HF.
    rewrite_rules = [
        IS_PAIR_ORD_INTERNAL_DEF,
        SUBSTITUTE_AT_EQ,
        SUBSTITUTE_AT_INSERT,
        SUBSTITUTE_AT_EMPTY,
        SUBSTITUTE_QUOTE_HF,
        _SUBST_VX_AT_X,
        _SUBST_VY_AT_Y,
        _SUBST_VZ_AT_Z,
        _SUBST_VY_AT_X,
        _SUBST_VZ_AT_X,
        _SUBST_VZ_AT_Y,
    ]
    p.have(
        "h_subst3: substitute (substitute (substitute "
        "  is_Pair_ord_internal (quote_hf x) idx_x) "
        "  (quote_hf y) idx_y) "
        "  (quote_hf (Pair_ord x y)) idx_z "
        "= Eq_f (quote_hf (Pair_ord x y)) "
        "       (Insert_t (Insert_t (quote_hf x) Empty_t) "
        "                 (Insert_t (Insert_t (quote_hf x) "
        "                                     (Insert_t (quote_hf y) Empty_t)) "
        "                           Empty_t))"
    ).by_rewrite(rewrite_rules)

    # QUOTE_HF_AT_PAIR_ORD bridges quote_hf (Pair_ord x y) into the
    # canonical Insert tower; substituting reduces the Eq_f to Eq_f T T.
    p.have(
        "h_qhf: quote_hf (Pair_ord x y) "
        "= Insert_t (Insert_t (quote_hf x) Empty_t) "
        "          (Insert_t (Insert_t (quote_hf x) "
        "                              (Insert_t (quote_hf y) Empty_t)) "
        "                    Empty_t)"
    ).by(QUOTE_HF_AT_PAIR_ORD, "x", "y", "hxy")

    p.have(
        "h_subst3_refl: substitute (substitute (substitute "
        "  is_Pair_ord_internal (quote_hf x) idx_x) "
        "  (quote_hf y) idx_y) "
        "  (quote_hf (Pair_ord x y)) idx_z "
        "= Eq_f (Insert_t (Insert_t (quote_hf x) Empty_t) "
        "                 (Insert_t (Insert_t (quote_hf x) "
        "                                     (Insert_t (quote_hf y) Empty_t)) "
        "                           Empty_t)) "
        "       (Insert_t (Insert_t (quote_hf x) Empty_t) "
        "                 (Insert_t (Insert_t (quote_hf x) "
        "                                     (Insert_t (quote_hf y) Empty_t)) "
        "                           Empty_t))"
    ).by_rewrite_of("h_subst3", ["h_qhf"])

    # Build is_term for the Insert tower from IS_TERM_QUOTE_HF +
    # IS_TERM_INSERT + IS_TERM_EMPTY.
    p.have("h_is_term_qx: is_term (quote_hf x)").by(IS_TERM_QUOTE_HF, "x")
    p.have("h_is_term_qy: is_term (quote_hf y)").by(IS_TERM_QUOTE_HF, "y")
    p.have("h_is_term_empty: is_term Empty_t").by_thm(IS_TERM_EMPTY)
    # Inner: Insert_t (quote_hf y) Empty_t.
    p.have(
        "h_is_term_qy_empty: is_term (Insert_t (quote_hf y) Empty_t)"
    ).by(
        IS_TERM_INSERT,
        "quote_hf y",
        "Empty_t",
        CONJ(p.fact("h_is_term_qy"), p.fact("h_is_term_empty")),
    )
    # Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t).
    p.have(
        "h_is_term_pair: is_term "
        "(Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t))"
    ).by(
        IS_TERM_INSERT,
        "quote_hf x",
        "Insert_t (quote_hf y) Empty_t",
        CONJ(p.fact("h_is_term_qx"), p.fact("h_is_term_qy_empty")),
    )
    # Insert_t (Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t)) Empty_t.
    p.have(
        "h_is_term_pair_singleton: is_term "
        "(Insert_t "
        "  (Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t)) "
        "  Empty_t)"
    ).by(
        IS_TERM_INSERT,
        "Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t)",
        "Empty_t",
        CONJ(p.fact("h_is_term_pair"), p.fact("h_is_term_empty")),
    )
    # Insert_t (quote_hf x) Empty_t.
    p.have(
        "h_is_term_qx_empty: is_term (Insert_t (quote_hf x) Empty_t)"
    ).by(
        IS_TERM_INSERT,
        "quote_hf x",
        "Empty_t",
        CONJ(p.fact("h_is_term_qx"), p.fact("h_is_term_empty")),
    )
    # The full Kuratowski tower T.
    p.have(
        "h_is_term_T: is_term "
        "(Insert_t (Insert_t (quote_hf x) Empty_t) "
        "          (Insert_t "
        "             (Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t)) "
        "             Empty_t))"
    ).by(
        IS_TERM_INSERT,
        "Insert_t (quote_hf x) Empty_t",
        "Insert_t (Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t)) Empty_t",
        CONJ(p.fact("h_is_term_qx_empty"), p.fact("h_is_term_pair_singleton")),
    )
    # PROV_HF_REFL at T.
    p.have(
        "h_refl: Prov_HF (Eq_f "
        "(Insert_t (Insert_t (quote_hf x) Empty_t) "
        "          (Insert_t "
        "             (Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t)) "
        "             Empty_t)) "
        "(Insert_t (Insert_t (quote_hf x) Empty_t) "
        "          (Insert_t "
        "             (Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t)) "
        "             Empty_t)))"
    ).by(
        PROV_HF_REFL,
        "Insert_t (Insert_t (quote_hf x) Empty_t) "
        "(Insert_t "
        "  (Insert_t (quote_hf x) (Insert_t (quote_hf y) Empty_t)) "
        "  Empty_t)",
        "h_is_term_T",
    )
    # Final: lift refl back through h_subst3_refl.
    p.thus(
        "Prov_HF (substitute (substitute (substitute "
        "  is_Pair_ord_internal (quote_hf x) idx_x) "
        "  (quote_hf y) idx_y) "
        "  (quote_hf (Pair_ord x y)) idx_z)"
    ).by_rewrite_of("h_refl", [SYM(p.fact("h_subst3_refl"))])


# B1.0 (c) -- In representability.
# Needed by HF-set proof-object representability and quote-layer
# membership reasoning.
#
# Body: ``In_a var_x var_y`` -- the syntactic HF membership atom.
# Substituting (quote_hf x, quote_hf y) into (var_x, var_y) yields the
# concrete membership claim ``In_a (quote_hf x) (quote_hf y)`` whose
# Prov_HF status mirrors HOL ``In x y``.
IS_IN_INTERNAL_DEF = define(
    "is_In_internal",
    nat0_ty,
    "In_a var_x var_y",
)
is_In_internal = mk_const("is_In_internal", [])


# QUOTE_HF_MEM_DECISION lives in ``hf_repr_thms.py`` (the high layer).
# Substitute representability is now readability-first: a scoped syntax
# recursion package supplies the constructor-local HF proof rules directly,
# rather than encoding finite computation histories.


# Fixed internal predicate bodies.
#
# Each ``*_internal`` constant below is a single HF formula code.  Predicate
# arguments are supplied by object-level substitution into the reserved free
# slots:
#
#   arity 1: var_x
#   arity 2: var_x, var_y
#   arity 3: var_x, var_y, var_z
#   arity 4: var_x, var_y, var_z, var_w
#
# Bound helper variables are deliberately allocated in high numeric bands so
# later template substitutions do not capture package-local variables.


def _V_idx(i):
    return mk_app(Var_t, _idx_term(i))


def _subst1(phi, x):
    return mk_app(substitute, phi, x, idx_x)


def _subst2(phi, x, y):
    return mk_app(substitute, _subst1(phi, x), y, idx_y)


def _subst3(phi, x, y, z):
    return mk_app(substitute, _subst2(phi, x, y), z, idx_z)


def _subst4(phi, x, y, z, w):
    return mk_app(substitute, _subst3(phi, x, y, z), w, idx_w)


def _entry_term(inp, out):
    return qparse("Pair_ord(inp,out)", inp=inp, out=out)


def _entry_in_graph(inp, out, graph):
    return mk_app(In_a, _entry_term(inp, out), graph)


def _support_code_empty():
    return qparse("Empty_t")


def _support_code_var(x):
    return qparse("Var_t(x)", x=x)


def _support_code_insert(a, b):
    return qparse("Insert_t(a,b)", a=a, b=b)


def _support_code_eq_f(a, b):
    return qparse("Eq_f(a,b)", a=a, b=b)


def _support_code_in_a(a, b):
    return qparse("In_a(a,b)", a=a, b=b)


def _support_code_not(p):
    return qparse("Not_f(p)", p=p)


def _support_code_imp(p, q):
    return qparse("Imp_f(p,q)", p=p, q=q)


def _support_code_forall(x, p):
    return qparse("Forall_f(x,p)", x=x, p=p)


def _support_term_local_body(set_var, node):
    x = _V_idx(11)
    a = _V_idx(12)
    b = _V_idx(13)
    return Q_or_chain(
        Q_eq(node, _support_code_empty()),
        Q_exists(_idx_term(11), Q_eq(node, _support_code_var(x))),
        Q_exists_chain(
            [_idx_term(12), _idx_term(13)],
            Q_and_chain(
                Q_eq(node, _support_code_insert(a, b)),
                mk_app(In_a, a, set_var),
                mk_app(In_a, b, set_var),
            ),
        ),
    )


def _support_term_closure_body(set_var):
    u = _V_idx(9)
    return Q_forall(
        _idx_term(9),
        Q_imp(mk_app(In_a, u, set_var), _support_term_local_body(set_var, u)),
    )


def _build_is_term_internal_body():
    n = var_x
    S = _V_idx(4)
    return Q_exists(
        _idx_term(4),
        Q_and(mk_app(In_a, n, S), _support_term_closure_body(S)),
    )


IS_TERM_INTERNAL_DEF = define(
    "is_term_internal",
    nat0_ty,
    _build_is_term_internal_body(),
)
is_term_internal = mk_const("is_term_internal", [])


def _support_form_local_body(term_set, form_set, node):
    a = _V_idx(12)
    b = _V_idx(13)
    p0 = _V_idx(16)
    q0 = _V_idx(17)
    x = _V_idx(11)
    return Q_or_chain(
        Q_exists_chain(
            [_idx_term(12), _idx_term(13)],
            Q_and_chain(
                Q_eq(node, _support_code_eq_f(a, b)),
                mk_app(In_a, a, term_set),
                mk_app(In_a, b, term_set),
            ),
        ),
        Q_exists(
            _idx_term(16),
            Q_and(Q_eq(node, _support_code_not(p0)), mk_app(In_a, p0, form_set)),
        ),
        Q_exists_chain(
            [_idx_term(16), _idx_term(17)],
            Q_and_chain(
                Q_eq(node, _support_code_imp(p0, q0)),
                mk_app(In_a, p0, form_set),
                mk_app(In_a, q0, form_set),
            ),
        ),
        Q_exists_chain(
            [_idx_term(11), _idx_term(16)],
            Q_and(Q_eq(node, _support_code_forall(x, p0)), mk_app(In_a, p0, form_set)),
        ),
        Q_exists_chain(
            [_idx_term(12), _idx_term(13)],
            Q_and_chain(
                Q_eq(node, _support_code_in_a(a, b)),
                mk_app(In_a, a, term_set),
                mk_app(In_a, b, term_set),
            ),
        ),
    )


def _support_form_closure_body(term_set, form_set):
    u = _V_idx(9)
    return Q_forall(
        _idx_term(9),
        Q_imp(
            mk_app(In_a, u, form_set),
            _support_form_local_body(term_set, form_set, u),
        ),
    )


def _build_is_form_internal_body():
    n = var_x
    T = _V_idx(5)
    F = _V_idx(6)
    return Q_exists_chain(
        [_idx_term(5), _idx_term(6)],
        Q_and_chain(
            mk_app(In_a, n, F),
            _support_term_closure_body(T),
            _support_form_closure_body(T, F),
        ),
    )


IS_FORM_INTERNAL_DEF = define(
    "is_form_internal",
    nat0_ty,
    _build_is_form_internal_body(),
)
is_form_internal = mk_const("is_form_internal", [])


def _support_free_step_body(path_set, node, needle):
    a = _V_idx(12)
    b = _V_idx(13)
    p0 = _V_idx(16)
    q0 = _V_idx(17)
    x = _V_idx(11)
    return Q_or_chain(
        Q_eq(node, _support_code_var(needle)),
        Q_exists_chain(
            [_idx_term(12), _idx_term(13)],
            Q_and(
                Q_eq(node, _support_code_insert(a, b)),
                Q_or(mk_app(In_a, a, path_set), mk_app(In_a, b, path_set)),
            ),
        ),
        Q_exists_chain(
            [_idx_term(12), _idx_term(13)],
            Q_and(
                Q_eq(node, _support_code_eq_f(a, b)),
                Q_or(mk_app(In_a, a, path_set), mk_app(In_a, b, path_set)),
            ),
        ),
        Q_exists_chain(
            [_idx_term(12), _idx_term(13)],
            Q_and(
                Q_eq(node, _support_code_in_a(a, b)),
                Q_or(mk_app(In_a, a, path_set), mk_app(In_a, b, path_set)),
            ),
        ),
        Q_exists(
            _idx_term(16),
            Q_and(Q_eq(node, _support_code_not(p0)), mk_app(In_a, p0, path_set)),
        ),
        Q_exists_chain(
            [_idx_term(16), _idx_term(17)],
            Q_and(
                Q_eq(node, _support_code_imp(p0, q0)),
                Q_or(mk_app(In_a, p0, path_set), mk_app(In_a, q0, path_set)),
            ),
        ),
        Q_exists_chain(
            [_idx_term(11), _idx_term(16)],
            Q_and_chain(
                Q_eq(node, _support_code_forall(x, p0)),
                Q_not(Q_eq(needle, x)),
                mk_app(In_a, p0, path_set),
            ),
        ),
    )


def _build_free_in_internal_body():
    n = var_x
    v = var_y
    W = _V_idx(7)
    u = _V_idx(9)
    return Q_exists(
        _idx_term(7),
        Q_and(
            mk_app(In_a, n, W),
            Q_forall(
                _idx_term(9),
                Q_imp(mk_app(In_a, u, W), _support_free_step_body(W, u, v)),
            ),
        ),
    )


FREE_IN_INTERNAL_DEF = define(
    "free_in_internal",
    nat0_ty,
    _build_free_in_internal_body(),
)
free_in_internal = mk_const("free_in_internal", [])


def _support_subst_binary_case(graph, node, out, ctor_code):
    a = _V_idx(12)
    b = _V_idx(13)
    ar = _V_idx(14)
    br = _V_idx(15)
    return Q_exists_chain(
        [_idx_term(12), _idx_term(13), _idx_term(14), _idx_term(15)],
        Q_and_chain(
            Q_eq(node, ctor_code(a, b)),
            _entry_in_graph(a, ar, graph),
            _entry_in_graph(b, br, graph),
            Q_eq(out, ctor_code(ar, br)),
        ),
    )


def _support_subst_step_body(graph, node, term, var, out):
    x = _V_idx(11)
    p0 = _V_idx(16)
    q0 = _V_idx(17)
    pr = _V_idx(18)
    qr = _V_idx(19)
    return Q_or_chain(
        Q_and(Q_eq(node, _support_code_empty()), Q_eq(out, _support_code_empty())),
        Q_exists(
            _idx_term(11),
            Q_and_chain(
                Q_eq(node, _support_code_var(x)),
                Q_eq(var, x),
                Q_eq(out, term),
            ),
        ),
        Q_exists(
            _idx_term(11),
            Q_and_chain(
                Q_eq(node, _support_code_var(x)),
                Q_not(Q_eq(var, x)),
                Q_eq(out, _support_code_var(x)),
            ),
        ),
        _support_subst_binary_case(graph, node, out, _support_code_insert),
        _support_subst_binary_case(graph, node, out, _support_code_eq_f),
        _support_subst_binary_case(graph, node, out, _support_code_in_a),
        Q_exists_chain(
            [_idx_term(16), _idx_term(18)],
            Q_and_chain(
                Q_eq(node, _support_code_not(p0)),
                _entry_in_graph(p0, pr, graph),
                Q_eq(out, _support_code_not(pr)),
            ),
        ),
        Q_exists_chain(
            [_idx_term(16), _idx_term(17), _idx_term(18), _idx_term(19)],
            Q_and_chain(
                Q_eq(node, _support_code_imp(p0, q0)),
                _entry_in_graph(p0, pr, graph),
                _entry_in_graph(q0, qr, graph),
                Q_eq(out, _support_code_imp(pr, qr)),
            ),
        ),
        Q_exists_chain(
            [_idx_term(11), _idx_term(16)],
            Q_and_chain(
                Q_eq(node, _support_code_forall(x, p0)),
                Q_eq(var, x),
                Q_eq(out, _support_code_forall(x, p0)),
            ),
        ),
        Q_exists_chain(
            [_idx_term(11), _idx_term(16), _idx_term(18)],
            Q_and_chain(
                Q_eq(node, _support_code_forall(x, p0)),
                Q_not(Q_eq(var, x)),
                _entry_in_graph(p0, pr, graph),
                Q_eq(out, _support_code_forall(x, pr)),
            ),
        ),
    )


def _build_substitute_internal_body():
    n = var_x
    t = var_y
    v = var_z
    r = var_w
    G = _V_idx(8)
    u = _V_idx(9)
    out = _V_idx(10)
    return Q_exists(
        _idx_term(8),
        Q_and(
            _entry_in_graph(n, r, G),
            Q_forall(
                _idx_term(9),
                Q_forall(
                    _idx_term(10),
                    Q_imp(
                        _entry_in_graph(u, out, G),
                        _support_subst_step_body(G, u, t, v, out),
                    ),
                ),
            ),
        ),
    )


# Fixed internal formula with slots:
#   var_x = F, var_y = t, var_z = v, var_w = result.
SUBSTITUTE_INTERNAL_DEF = define(
    "substitute_internal",
    nat0_ty,
    _build_substitute_internal_body(),
)
substitute_internal = mk_const("substitute_internal", [])


TEMPLATE_FILL_DEF, TEMPLATE_FILL_AT = define_with_at(
    "template_fill",
    parse_type("nat0 -> nat0 -> nat0 -> nat0"),
    "\\D:nat0. \\t:nat0. \\v:nat0. substitute D t v",
)
template_fill = mk_const("template_fill", [])


TEMPLATE_FILL_INTERNAL_DEF = define(
    "template_fill_internal",
    nat0_ty,
    "substitute_internal",
)
template_fill_internal = mk_const("template_fill_internal", [])


def _substitute_internal_rel(F, t, v, r):
    """Surface text for ``substitute_internal(F,t,v,r)`` at HF quotes."""
    return (
        "(substitute (substitute (substitute (substitute "
        f"substitute_internal (quote_hf ({F})) idx_x) "
        f"(quote_hf ({t})) idx_y) "
        f"(quote_hf ({v})) idx_z) "
        f"(quote_hf ({r})) idx_w)"
    )


def _prov_substitute_internal_rel(F, t, v, r):
    return f"Prov_HF {_substitute_internal_rel(F, t, v, r)}"


def _is_term_internal_rel(n):
    return f"(substitute is_term_internal (quote_hf ({n})) idx_x)"


def _prov_is_term_internal_rel(n):
    return f"Prov_HF {_is_term_internal_rel(n)}"


def _is_form_internal_rel(n):
    return f"(substitute is_form_internal (quote_hf ({n})) idx_x)"


def _prov_is_form_internal_rel(n):
    return f"Prov_HF {_is_form_internal_rel(n)}"


def _free_in_internal_rel(F, v):
    return (
        "(substitute (substitute "
        f"free_in_internal (quote_hf ({F})) idx_x) "
        f"(quote_hf ({v})) idx_y)"
    )


def _prov_free_in_internal_rel(F, v):
    return f"Prov_HF {_free_in_internal_rel(F, v)}"


def _template_fill_internal_rel(D, t, v, r):
    """Surface text for ``template_fill_internal(D,t,v,r)`` at HF quotes."""
    return (
        "(substitute (substitute (substitute (substitute "
        f"template_fill_internal (quote_hf ({D})) idx_x) "
        f"(quote_hf ({t})) idx_y) "
        f"(quote_hf ({v})) idx_z) "
        f"(quote_hf ({r})) idx_w)"
    )


def _prov_template_fill_internal_rel(D, t, v, r):
    return f"Prov_HF {_template_fill_internal_rel(D, t, v, r)}"


_SUBST_RULE_EMPTY = f"!t v. {_prov_substitute_internal_rel('Empty_t', 't', 'v', 'Empty_t')}"
_SUBST_RULE_VAR_HIT = (
    f"!x t v. x = v ==> {_prov_substitute_internal_rel('Var_t x', 't', 'v', 't')}"
)
_SUBST_RULE_VAR_MISS = (
    f"!x t v. ~(x = v) ==> "
    f"{_prov_substitute_internal_rel('Var_t x', 't', 'v', 'Var_t x')}"
)
_SUBST_RULE_INSERT = (
    f"!a b t v ar br. "
    f"{_prov_substitute_internal_rel('a', 't', 'v', 'ar')} ==> "
    f"{_prov_substitute_internal_rel('b', 't', 'v', 'br')} ==> "
    f"{_prov_substitute_internal_rel('Insert_t a b', 't', 'v', 'Insert_t ar br')}"
)
_SUBST_RULE_EQ = (
    f"!a b t v ar br. "
    f"{_prov_substitute_internal_rel('a', 't', 'v', 'ar')} ==> "
    f"{_prov_substitute_internal_rel('b', 't', 'v', 'br')} ==> "
    f"{_prov_substitute_internal_rel('Eq_f a b', 't', 'v', 'Eq_f ar br')}"
)
_SUBST_RULE_IN = (
    f"!a b t v ar br. "
    f"{_prov_substitute_internal_rel('a', 't', 'v', 'ar')} ==> "
    f"{_prov_substitute_internal_rel('b', 't', 'v', 'br')} ==> "
    f"{_prov_substitute_internal_rel('In_a a b', 't', 'v', 'In_a ar br')}"
)
_SUBST_RULE_NOT = (
    f"!phi t v phi_r. "
    f"{_prov_substitute_internal_rel('phi', 't', 'v', 'phi_r')} ==> "
    f"{_prov_substitute_internal_rel('Not_f phi', 't', 'v', 'Not_f phi_r')}"
)
_SUBST_RULE_IMP = (
    f"!p q t v pr qr. "
    f"{_prov_substitute_internal_rel('p', 't', 'v', 'pr')} ==> "
    f"{_prov_substitute_internal_rel('q', 't', 'v', 'qr')} ==> "
    f"{_prov_substitute_internal_rel('Imp_f p q', 't', 'v', 'Imp_f pr qr')}"
)
_SUBST_RULE_FORALL_HIT = (
    f"!w body t v. w = v ==> "
    f"{_prov_substitute_internal_rel('Forall_f w body', 't', 'v', 'Forall_f w body')}"
)
_SUBST_RULE_FORALL_MISS = (
    f"!w body t v body_r. ~(w = v) ==> "
    f"{_prov_substitute_internal_rel('body', 't', 'v', 'body_r')} ==> "
    f"{_prov_substitute_internal_rel('Forall_f w body', 't', 'v', 'Forall_f w body_r')}"
)
_SUBST_HEADLINE_SYNTACTIC = (
    f"!F t v. (is_term F \\/ is_form F) ==> "
    f"{_prov_substitute_internal_rel('F', 't', 'v', '((substitute F) t) v')}"
)


_SUPPORT_RULE_IS_TERM_POS = f"!n. is_term n ==> {_prov_is_term_internal_rel('n')}"
_SUPPORT_RULE_IS_TERM_NEG = (
    f"!n. ~(is_term n) ==> Prov_HF (Not_f {_is_term_internal_rel('n')})"
)
_SUPPORT_RULE_IS_FORM_POS = f"!n. is_form n ==> {_prov_is_form_internal_rel('n')}"
_SUPPORT_RULE_IS_FORM_NEG = (
    f"!n. ~(is_form n) ==> Prov_HF (Not_f {_is_form_internal_rel('n')})"
)
_SUPPORT_RULE_FREE_IN_POS = f"!F v. free_in F v ==> {_prov_free_in_internal_rel('F', 'v')}"
_SUPPORT_RULE_FREE_IN_NEG = (
    f"!F v. ~(free_in F v) ==> Prov_HF (Not_f {_free_in_internal_rel('F', 'v')})"
)


# Support-predicate package for the finite certificate bodies above.
# ``substitute_internal`` is handled by ``HF_SYNTAX_REC_PACKAGE`` below; this
# package supplies the remaining support predicates consumed by
# is_axiom_internal and the final Prov_HF representability proof.
def _right_assoc_conj_text(items):
    out = items[-1]
    for item in reversed(items[:-1]):
        out = f"({item}) /\\ ({out})"
    return out


HF_SUPPORT_PREDICATE_PACKAGE = new_axiom(
    parse(
        _right_assoc_conj_text(
            [
                _SUPPORT_RULE_IS_TERM_POS,
                _SUPPORT_RULE_IS_TERM_NEG,
                _SUPPORT_RULE_IS_FORM_POS,
                _SUPPORT_RULE_IS_FORM_NEG,
                _SUPPORT_RULE_FREE_IN_POS,
                _SUPPORT_RULE_FREE_IN_NEG,
            ]
        )
    )
)


def _support_pkg_clause(index, count=6):
    th = HF_SUPPORT_PREDICATE_PACKAGE
    for _ in range(index):
        th = CONJUNCT2(th)
    if index < count - 1:
        return CONJUNCT1(th)
    return th


IS_TERM_INTERNAL_REPRESENTS = _support_pkg_clause(0)
NOT_IS_TERM_INTERNAL_REPRESENTS = _support_pkg_clause(1)
IS_FORM_INTERNAL_REPRESENTS = _support_pkg_clause(2)
NOT_IS_FORM_INTERNAL_REPRESENTS = _support_pkg_clause(3)
FREE_IN_INTERNAL_REPRESENTS = _support_pkg_clause(4)
NOT_FREE_IN_INTERNAL_REPRESENTS = _support_pkg_clause(5)


# Constructor-local rules generated by the scoped syntax-recursion package.
SUBSTITUTE_REC_EMPTY = new_axiom(parse(_SUBST_RULE_EMPTY))
SUBSTITUTE_REC_VAR_HIT = new_axiom(parse(_SUBST_RULE_VAR_HIT))
SUBSTITUTE_REC_VAR_MISS = new_axiom(parse(_SUBST_RULE_VAR_MISS))
SUBSTITUTE_REC_INSERT = new_axiom(parse(_SUBST_RULE_INSERT))
SUBSTITUTE_REC_EQ = new_axiom(parse(_SUBST_RULE_EQ))
SUBSTITUTE_REC_IN = new_axiom(parse(_SUBST_RULE_IN))
SUBSTITUTE_REC_NOT = new_axiom(parse(_SUBST_RULE_NOT))
SUBSTITUTE_REC_IMP = new_axiom(parse(_SUBST_RULE_IMP))
SUBSTITUTE_REC_FORALL_HIT = new_axiom(parse(_SUBST_RULE_FORALL_HIT))
SUBSTITUTE_REC_FORALL_MISS = new_axiom(parse(_SUBST_RULE_FORALL_MISS))


# Single accepted package axiom for readability-first G1. It is explicitly
# syntax-scoped; malformed nat0 values get no fake substitution semantics.
HF_SYNTAX_REC_PACKAGE = new_axiom(
    parse(
        f"({_SUBST_RULE_EMPTY}) ==> "
        f"({_SUBST_RULE_VAR_HIT}) ==> "
        f"({_SUBST_RULE_VAR_MISS}) ==> "
        f"({_SUBST_RULE_INSERT}) ==> "
        f"({_SUBST_RULE_EQ}) ==> "
        f"({_SUBST_RULE_IN}) ==> "
        f"({_SUBST_RULE_NOT}) ==> "
        f"({_SUBST_RULE_IMP}) ==> "
        f"({_SUBST_RULE_FORALL_HIT}) ==> "
        f"({_SUBST_RULE_FORALL_MISS}) ==> "
        f"({_SUBST_HEADLINE_SYNTACTIC})"
    )
)


def _derive_substitute_represents_syntactic():
    th = HF_SYNTAX_REC_PACKAGE
    for rule in [
        SUBSTITUTE_REC_EMPTY,
        SUBSTITUTE_REC_VAR_HIT,
        SUBSTITUTE_REC_VAR_MISS,
        SUBSTITUTE_REC_INSERT,
        SUBSTITUTE_REC_EQ,
        SUBSTITUTE_REC_IN,
        SUBSTITUTE_REC_NOT,
        SUBSTITUTE_REC_IMP,
        SUBSTITUTE_REC_FORALL_HIT,
        SUBSTITUTE_REC_FORALL_MISS,
    ]:
        th = MP(th, rule)
    return th


SUBSTITUTE_REPRESENTS_SYNTACTIC = _derive_substitute_represents_syntactic()


@proof
def SUBSTITUTE_REPRESENTS_TERM(p):
    """|- !phi t v. is_term phi ==> Prov_HF(substitute_internal phi t v ...)."""
    p.goal(
        f"!phi t v. is_term phi ==> "
        f"{_prov_substitute_internal_rel('phi', 't', 'v', '((substitute phi) t) v')}"
    )
    p.fix("phi t v")
    p.assume("hphi: is_term phi")
    p.have("hsyntax: is_term phi \\/ is_form phi").by_thm(
        DISJ1(p.fact("hphi"), p._parse("is_form phi"))
    )
    p.thus(_prov_substitute_internal_rel("phi", "t", "v", "((substitute phi) t) v")).by(
        SUBSTITUTE_REPRESENTS_SYNTACTIC, "phi", "t", "v", "hsyntax"
    )


@proof
def SUBSTITUTE_REPRESENTS_FORM(p):
    """|- !phi t v. is_form phi ==> Prov_HF(substitute_internal phi t v ...)."""
    p.goal(
        f"!phi t v. is_form phi ==> "
        f"{_prov_substitute_internal_rel('phi', 't', 'v', '((substitute phi) t) v')}"
    )
    p.fix("phi t v")
    p.assume("hphi: is_form phi")
    p.have("hsyntax: is_term phi \\/ is_form phi").by_thm(
        DISJ2(p._parse("is_term phi"), p.fact("hphi"))
    )
    p.thus(_prov_substitute_internal_rel("phi", "t", "v", "((substitute phi) t) v")).by(
        SUBSTITUTE_REPRESENTS_SYNTACTIC, "phi", "t", "v", "hsyntax"
    )


# Backward-compatible name for formula consumers, including the diagonal path.
SUBSTITUTE_REPRESENTS = SUBSTITUTE_REPRESENTS_FORM


# ---------------------------------------------------------------------------
# Stage 3C (b) -- quoted-data template filling.
#
# ``template_fill D t v`` is a readability layer for quoted data templates:
# it fills holes encoded as ``Var_t v`` while walking ``Empty_t`` /
# ``Insert_t`` data.  It is definitionally backed by ``substitute`` so the
# existing syntax-recursion package proves its internal relation, but callers
# can cite the template-specific name and rules instead of overloading the
# object-language substitution story.
# ---------------------------------------------------------------------------


@proof
def TEMPLATE_FILL_EMPTY(p):
    """|- !t v. template_fill Empty_t t v = Empty_t."""
    p.goal("!t v. template_fill Empty_t t v = Empty_t")
    p.fix("t v")
    p.thus("template_fill Empty_t t v = Empty_t").by_rewrite(
        [TEMPLATE_FILL_AT, SUBSTITUTE_AT_EMPTY]
    )


@proof
def TEMPLATE_FILL_HOLE_HIT(p):
    """|- !x t v. v = x ==> template_fill (Var_t x) t v = t."""
    p.goal("!x t v. v = x ==> template_fill (Var_t x) t v = t")
    p.fix("x t v")
    p.assume("hit: v = x")
    subst_hit = MP(
        SPECL([p._parse("x"), p._parse("t"), p._parse("v")], SUBSTITUTE_AT_VAR_HIT),
        p.fact("hit"),
    )
    p.thus("template_fill (Var_t x) t v = t").by_rewrite(
        [TEMPLATE_FILL_AT, subst_hit]
    )


@proof
def TEMPLATE_FILL_HOLE_MISS(p):
    """|- !x t v. ~(v = x) ==> template_fill (Var_t x) t v = Var_t x."""
    p.goal("!x t v. ~(v = x) ==> template_fill (Var_t x) t v = Var_t x")
    p.fix("x t v")
    p.assume("miss: ~(v = x)")
    subst_miss = MP(
        SPECL([p._parse("x"), p._parse("t"), p._parse("v")], SUBSTITUTE_AT_VAR_MISS),
        p.fact("miss"),
    )
    p.thus("template_fill (Var_t x) t v = Var_t x").by_rewrite(
        [TEMPLATE_FILL_AT, subst_miss]
    )


@proof
def TEMPLATE_FILL_INSERT(p):
    """|- !a b t v.
          template_fill (Insert_t a b) t v =
          Insert_t (template_fill a t v) (template_fill b t v)."""
    p.goal(
        "!a b t v. template_fill (Insert_t a b) t v "
        "= Insert_t (template_fill a t v) (template_fill b t v)"
    )
    p.fix("a b t v")
    p.thus(
        "template_fill (Insert_t a b) t v "
        "= Insert_t (template_fill a t v) (template_fill b t v)"
    ).by_rewrite([TEMPLATE_FILL_AT, SUBSTITUTE_AT_INSERT])


_qv_template = Var("qv", nat0_ty)
_template_fill_z_hit = MP(
    SPECL([_idx_z, _qv_template, _idx_z], TEMPLATE_FILL_HOLE_HIT),
    REFL(_idx_z),
)

TEMPLATE_FILL_QPARSE_VAR_T = GEN(
    _qv_template,
    REWRITE_PROVE(
        [
            TEMPLATE_FILL_INSERT,
            TEMPLATE_FILL_EMPTY,
            _template_fill_z_hit,
            VAR_Z_DEF,
            IDX_Z_DEF,
        ],
        mk_eq(
            mk_app(
                mk_app(
                    mk_app(
                        template_fill,
                        qparse("Var_t(var_z)", var_z=var_z),
                    ),
                    _qv_template,
                ),
                idx_z,
            ),
            qparse("Var_t(qv)", qv=_qv_template),
        ),
    ),
)
"""|- !qv. template_fill (qparse("Var_t(var_z)", var_z=var_z)) qv idx_z
          = qparse("Var_t(qv)", qv=qv).

Template smoke theorem for the motivating case: the placeholder is inside
quoted data, not inside an object-language ``Var_t`` node.
"""


@proof
def TEMPLATE_FILL_REPRESENTS_TERM(p):
    """|- !D t v. is_term D ==> Prov_HF(template_fill_internal D t v ...)."""
    p.goal(
        f"!D t v. is_term D ==> "
        f"{_prov_template_fill_internal_rel('D', 't', 'v', 'template_fill D t v')}"
    )
    p.fix("D t v")
    p.assume("hD: is_term D")
    p.have(
        "h_subst: "
        f"{_prov_substitute_internal_rel('D', 't', 'v', '((substitute D) t) v')}"
    ).by(SUBSTITUTE_REPRESENTS_TERM, "D", "t", "v", "hD")
    fill_at = SPECL([p._parse("D"), p._parse("t"), p._parse("v")], TEMPLATE_FILL_AT)
    p.thus(
        _prov_template_fill_internal_rel("D", "t", "v", "template_fill D t v")
    ).by_rewrite_of(
        "h_subst",
        [SYM(TEMPLATE_FILL_INTERNAL_DEF), SYM(fill_at)],
    )


TEMPLATE_FILL_REPRESENTS = TEMPLATE_FILL_REPRESENTS_TERM


# ---------------------------------------------------------------------------
# Stage 3D (a) -- internal provability predicate bodies.
#
# ``Prov_HF_internal`` is now a real dependency-set HF formula:
#
#   Prov_HF_internal(x) :=
#     ?P. Proof_HF_set_internal(P,x)
#
# where proof records are ``Pair_ord dependency_set formula`` and MP/Gen
# citations use ordinary HF membership in the dependency set.  The side
# condition and representability proofs still live in ``hf_repr_thms.py``
# because they need the high-level Prov_HF toolkit from ``hf_logic``.
# ---------------------------------------------------------------------------


def _is_term_internal_at(n):
    return _subst1(is_term_internal, n)


def _is_form_internal_at(n):
    return _subst1(is_form_internal, n)


def _free_in_internal_at(formula, v):
    return _subst2(free_in_internal, formula, v)


def _substitute_internal_at(formula, term, v, result):
    return _subst4(substitute_internal, formula, term, v, result)


def _proof_record(rank, formula):
    return qparse("Pair_ord(rank,formula)", rank=rank, formula=formula)


def _proof_record_in(rank, formula, proof_set):
    return mk_app(In_a, _proof_record(rank, formula), proof_set)


def _build_is_mp_internal_body():
    return Q_eq(
        var_y,
        qparse("Imp_f(premise,conclusion)", premise=var_x, conclusion=var_z),
    )


IS_MP_INTERNAL_DEF = define("is_mp_internal", nat0_ty, _build_is_mp_internal_body())
is_mp_internal = mk_const("is_mp_internal", [])


def _build_is_gen_internal_body():
    gen_x = _V_idx(34)
    return Q_exists(
        _idx_term(34),
        Q_eq(var_y, qparse("Forall_f(gen_x,premise)", gen_x=gen_x, premise=var_x)),
    )


IS_GEN_INTERNAL_DEF = define("is_gen_internal", nat0_ty, _build_is_gen_internal_body())
is_gen_internal = mk_const("is_gen_internal", [])


def _is_mp_internal_at(premise, implication, conclusion):
    return _subst3(is_mp_internal, premise, implication, conclusion)


def _is_gen_internal_at(premise, conclusion):
    return _subst2(is_gen_internal, premise, conclusion)


_AX_A = _V_idx(20)
_AX_B = _V_idx(21)
_AX_C = _V_idx(22)
_AX_F = _V_idx(23)
_AX_G = _V_idx(24)
_AX_t = _V_idx(25)
_AX_t1 = _V_idx(26)
_AX_t2 = _V_idx(27)
_AX_x = _V_idx(28)
_AX_R = _V_idx(29)
_AX_R1 = _V_idx(30)
_AX_R2 = _V_idx(31)
_AX_F0 = _V_idx(32)
_AX_F1 = _V_idx(33)


def _code_eq(target, code):
    return Q_eq(target, code)


def _build_is_hf_axiom_internal_body():
    h = var_x
    axiom_codes = [
        qparse("Forall_f(0,Not_f(In_a(Var_t(0),Empty_t)))"),
        qparse("Forall_f(0,Forall_f(1,In_a(Var_t(0),Insert_t(Var_t(0),Var_t(1)))))"),
        qparse(
            "Forall_f(0,Forall_f(1,Forall_f(2,"
            "Imp_f(Not_f(Eq_f(Var_t(0),Var_t(1))),"
            "Not_f(Imp_f("
            "Imp_f(In_a(Var_t(1),Insert_t(Var_t(0),Var_t(2))),In_a(Var_t(1),Var_t(2))),"
            "Not_f(Imp_f(In_a(Var_t(1),Var_t(2)),"
            "In_a(Var_t(1),Insert_t(Var_t(0),Var_t(2)))))))))))"
        ),
        qparse(
            "Forall_f(0,Forall_f(1,"
            "Imp_f(Forall_f(2,Not_f(Imp_f("
            "Imp_f(In_a(Var_t(2),Var_t(0)),In_a(Var_t(2),Var_t(1))),"
            "Not_f(Imp_f(In_a(Var_t(2),Var_t(1)),In_a(Var_t(2),Var_t(0))))))),"
            "Eq_f(Var_t(0),Var_t(1)))))"
        ),
        qparse(
            "Forall_f(0,Forall_f(1,"
            "Imp_f(In_a(Var_t(0),Var_t(1)),"
            "Not_f(Forall_f(2,Not_f(Eq_f(Var_t(1),Insert_t(Var_t(0),Var_t(2)))))))))"
        ),
    ]
    return Q_or_chain(*[_code_eq(h, code) for code in axiom_codes])


IS_HF_AXIOM_INTERNAL_DEF = define(
    "is_hf_axiom_internal",
    nat0_ty,
    _build_is_hf_axiom_internal_body(),
)
is_hf_axiom_internal = mk_const("is_hf_axiom_internal", [])


def _build_is_K_internal_body():
    h = var_x
    return Q_exists_chain(
        [_idx_term(20), _idx_term(21)],
        Q_and_chain(
            _is_form_internal_at(_AX_A),
            _is_form_internal_at(_AX_B),
            _code_eq(h, qparse("Imp_f(A,Imp_f(B,A))", A=_AX_A, B=_AX_B)),
        ),
    )


IS_K_INTERNAL_DEF = define("is_K_internal", nat0_ty, _build_is_K_internal_body())
is_K_internal = mk_const("is_K_internal", [])


def _build_is_S_internal_body():
    h = var_x
    return Q_exists_chain(
        [_idx_term(20), _idx_term(21), _idx_term(22)],
        Q_and_chain(
            _is_form_internal_at(_AX_A),
            _is_form_internal_at(_AX_B),
            _is_form_internal_at(_AX_C),
            _code_eq(
                h,
                qparse(
                    "Imp_f(Imp_f(A,Imp_f(B,C)),Imp_f(Imp_f(A,B),Imp_f(A,C)))",
                    A=_AX_A,
                    B=_AX_B,
                    C=_AX_C,
                ),
            ),
        ),
    )


IS_S_INTERNAL_DEF = define("is_S_internal", nat0_ty, _build_is_S_internal_body())
is_S_internal = mk_const("is_S_internal", [])


def _build_is_N_internal_body():
    h = var_x
    return Q_exists_chain(
        [_idx_term(20), _idx_term(21)],
        Q_and_chain(
            _is_form_internal_at(_AX_A),
            _is_form_internal_at(_AX_B),
            _code_eq(
                h,
                qparse(
                    "Imp_f(Imp_f(Not_f(B),Not_f(A)),Imp_f(A,B))",
                    A=_AX_A,
                    B=_AX_B,
                ),
            ),
        ),
    )


IS_N_INTERNAL_DEF = define("is_N_internal", nat0_ty, _build_is_N_internal_body())
is_N_internal = mk_const("is_N_internal", [])


def _build_is_UI_internal_body():
    h = var_x
    return Q_exists_chain(
        [_idx_term(28), _idx_term(23), _idx_term(25), _idx_term(29)],
        Q_and_chain(
            _is_form_internal_at(_AX_F),
            _is_term_internal_at(_AX_t),
            _substitute_internal_at(_AX_F, _AX_t, _AX_x, _AX_R),
            _code_eq(
                h,
                qparse("Imp_f(Forall_f(x,F),R)", x=_AX_x, F=_AX_F, R=_AX_R),
            ),
        ),
    )


IS_UI_INTERNAL_DEF = define("is_UI_internal", nat0_ty, _build_is_UI_internal_body())
is_UI_internal = mk_const("is_UI_internal", [])


def _build_is_Vac_internal_body():
    h = var_x
    return Q_exists_chain(
        [_idx_term(28), _idx_term(23)],
        Q_and_chain(
            _is_form_internal_at(_AX_F),
            Q_not(_free_in_internal_at(_AX_F, _AX_x)),
            _code_eq(h, qparse("Imp_f(F,Forall_f(x,F))", x=_AX_x, F=_AX_F)),
        ),
    )


IS_VAC_INTERNAL_DEF = define("is_Vac_internal", nat0_ty, _build_is_Vac_internal_body())
is_Vac_internal = mk_const("is_Vac_internal", [])


def _build_is_FaImp_internal_body():
    h = var_x
    return Q_exists_chain(
        [_idx_term(28), _idx_term(23), _idx_term(24)],
        Q_and_chain(
            _is_form_internal_at(_AX_F),
            _is_form_internal_at(_AX_G),
            Q_not(_free_in_internal_at(_AX_F, _AX_x)),
            _code_eq(
                h,
                qparse(
                    "Imp_f(Forall_f(x,Imp_f(F,G)),Imp_f(F,Forall_f(x,G)))",
                    x=_AX_x,
                    F=_AX_F,
                    G=_AX_G,
                ),
            ),
        ),
    )


IS_FAIMP_INTERNAL_DEF = define(
    "is_FaImp_internal",
    nat0_ty,
    _build_is_FaImp_internal_body(),
)
is_FaImp_internal = mk_const("is_FaImp_internal", [])


def _build_is_Refl_internal_body():
    h = var_x
    return Q_exists(
        _idx_term(25),
        Q_and(_is_term_internal_at(_AX_t), _code_eq(h, qparse("Eq_f(t,t)", t=_AX_t))),
    )


IS_REFL_INTERNAL_DEF = define("is_Refl_internal", nat0_ty, _build_is_Refl_internal_body())
is_Refl_internal = mk_const("is_Refl_internal", [])


def _build_is_Subst_internal_body():
    h = var_x
    return Q_exists_chain(
        [
            _idx_term(28),
            _idx_term(23),
            _idx_term(26),
            _idx_term(27),
            _idx_term(30),
            _idx_term(31),
        ],
        Q_and_chain(
            _is_form_internal_at(_AX_F),
            _is_term_internal_at(_AX_t1),
            _is_term_internal_at(_AX_t2),
            _substitute_internal_at(_AX_F, _AX_t1, _AX_x, _AX_R1),
            _substitute_internal_at(_AX_F, _AX_t2, _AX_x, _AX_R2),
            _code_eq(
                h,
                qparse(
                    "Imp_f(Eq_f(t1,t2),Imp_f(R1,R2))",
                    t1=_AX_t1,
                    t2=_AX_t2,
                    R1=_AX_R1,
                    R2=_AX_R2,
                ),
            ),
        ),
    )


IS_SUBST_INTERNAL_DEF = define(
    "is_Subst_internal",
    nat0_ty,
    _build_is_Subst_internal_body(),
)
is_Subst_internal = mk_const("is_Subst_internal", [])


def _build_is_logical_axiom_internal_body():
    h = var_x
    return Q_or_chain(
        _subst1(is_K_internal, h),
        _subst1(is_S_internal, h),
        _subst1(is_N_internal, h),
        _subst1(is_UI_internal, h),
        _subst1(is_Vac_internal, h),
        _subst1(is_Refl_internal, h),
        _subst1(is_Subst_internal, h),
        _subst1(is_FaImp_internal, h),
    )


IS_LOGICAL_AXIOM_INTERNAL_DEF = define(
    "is_logical_axiom_internal",
    nat0_ty,
    _build_is_logical_axiom_internal_body(),
)
is_logical_axiom_internal = mk_const("is_logical_axiom_internal", [])


def _build_is_hf_ind_axiom_internal_body():
    h = var_x
    idx0 = qparse("0")
    idx1 = qparse("1")
    idx2 = qparse("2")
    member_var = qparse("Var_t(0)")
    current_var = qparse("Var_t(1)")
    step_code = qparse(
        "Forall_f(1,Imp_f(Forall_f(0,Imp_f(In_a(Var_t(0),Var_t(1)),F0)),F1))",
        F0=_AX_F0,
        F1=_AX_F1,
    )
    conclusion_code = qparse("Forall_f(1,F1)", F1=_AX_F1)
    return Q_exists_chain(
        [_idx_term(23), _idx_term(32), _idx_term(33)],
        Q_and_chain(
            _is_form_internal_at(_AX_F),
            Q_not(_free_in_internal_at(_AX_F, idx0)),
            Q_not(_free_in_internal_at(_AX_F, idx1)),
            _substitute_internal_at(_AX_F, member_var, idx2, _AX_F0),
            _substitute_internal_at(_AX_F, current_var, idx2, _AX_F1),
            _code_eq(
                h,
                qparse("Imp_f(step,conclusion)", step=step_code, conclusion=conclusion_code),
            ),
        ),
    )


IS_HF_IND_AXIOM_INTERNAL_DEF = define(
    "is_hf_ind_axiom_internal",
    nat0_ty,
    _build_is_hf_ind_axiom_internal_body(),
)
is_hf_ind_axiom_internal = mk_const("is_hf_ind_axiom_internal", [])


def _build_is_axiom_internal_body():
    h = var_x
    return Q_or_chain(
        _subst1(is_hf_axiom_internal, h),
        _subst1(is_hf_ind_axiom_internal, h),
        _subst1(is_logical_axiom_internal, h),
    )


IS_AXIOM_INTERNAL_DEF = define("is_axiom_internal", nat0_ty, _build_is_axiom_internal_body())
is_axiom_internal = mk_const("is_axiom_internal", [])


def _build_valid_step_hf_set_internal_body():
    P = var_x
    k = var_y
    h = var_z
    m_i = _V_idx(40)
    m_f = _V_idx(41)
    m_j = _V_idx(42)
    m_g = _V_idx(43)
    g_i = _V_idx(44)
    g_f = _V_idx(45)
    mp_case = Q_exists_chain(
        [_idx_term(40), _idx_term(41), _idx_term(42), _idx_term(43)],
        Q_and_chain(
            _proof_record_in(m_i, m_f, P),
            _proof_record_in(m_j, m_g, P),
            mk_app(In_a, m_i, k),
            mk_app(In_a, m_j, k),
            _is_mp_internal_at(m_f, m_g, h),
        ),
    )
    gen_case = Q_exists_chain(
        [_idx_term(44), _idx_term(45)],
        Q_and_chain(
            _proof_record_in(g_i, g_f, P),
            mk_app(In_a, g_i, k),
            _is_gen_internal_at(g_f, h),
        ),
    )
    return Q_or_chain(_subst1(is_axiom_internal, h), mp_case, gen_case)


VALID_STEP_HF_SET_INTERNAL_DEF = define(
    "valid_step_hf_set_internal",
    nat0_ty,
    _build_valid_step_hf_set_internal_body(),
)
valid_step_hf_set_internal = mk_const("valid_step_hf_set_internal", [])


def _valid_step_hf_set_internal_at(P, k, h):
    return _subst3(valid_step_hf_set_internal, P, k, h)


def _build_proof_hf_set_internal_body():
    P = var_x
    n = var_y
    k = _V_idx(46)
    j = _V_idx(47)
    h = _V_idx(48)
    return Q_exists(
        _idx_term(46),
        Q_and(
            _proof_record_in(k, n, P),
            Q_forall(
                _idx_term(47),
                Q_forall(
                    _idx_term(48),
                    Q_imp(
                        _proof_record_in(j, h, P),
                        _valid_step_hf_set_internal_at(P, j, h),
                    ),
                ),
            ),
        ),
    )


PROOF_HF_SET_INTERNAL_DEF = define(
    "Proof_HF_set_internal",
    nat0_ty,
    _build_proof_hf_set_internal_body(),
)
Proof_HF_set_internal = mk_const("Proof_HF_set_internal", [])


def _proof_hf_set_internal_at(P, n):
    return _subst2(Proof_HF_set_internal, P, n)


def _build_prov_hf_internal_body():
    P = _V_idx(49)
    return Q_exists(_idx_term(49), _proof_hf_set_internal_at(P, var_x))


PROV_HF_INTERNAL_DEF = define(
    "Prov_HF_internal",
    nat0_ty,
    _build_prov_hf_internal_body(),
)
Prov_HF_internal = mk_const("Prov_HF_internal", [])


# ---------------------------------------------------------------------------
# Stage 3D (b) -- helper for the diagonal lemma.
# ---------------------------------------------------------------------------


# substitute_2 helper -- compose two substitutes; used by Stage 4 to
# express "phi(x, y) with both x and y substituted by numerals".
_F_s2 = Var("F", nat0_ty)
_a_s2 = Var("a", nat0_ty)
_b_s2 = Var("b", nat0_ty)
_vx_s2 = Var("vx", nat0_ty)
_vy_s2 = Var("vy", nat0_ty)


SUBSTITUTE_2_DEF = define(
    "substitute_2",
    parse_type("nat0 -> nat0 -> nat0 -> nat0 -> nat0 -> nat0"),
    mk_abs(
        _F_s2,
        mk_abs(
            _a_s2,
            mk_abs(
                _b_s2,
                mk_abs(
                    _vx_s2,
                    mk_abs(
                        _vy_s2,
                        mk_app(
                            substitute,
                            mk_app(substitute, _F_s2, _a_s2, _vx_s2),
                            _b_s2,
                            _vy_s2,
                        ),
                    ),
                ),
            ),
        ),
    ),
)
substitute_2 = mk_const("substitute_2", [])


# PROV_HF_REPRESENTS, IS_FORM_PROV_HF_INTERNAL, FREE_IN_PROV_HF_INTERNAL
# proof scripts live in hf_repr_thms.py.


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 3A (a) -- numeral function.")
    print("    NUMERAL_BASE :", pp_thm(NUMERAL_BASE))
    print("    NUMERAL_STEP :", pp_thm(NUMERAL_STEP))
    print()
    print("    (Numerals encode as von Neumann ordinals: 0 := Empty_t,")
    print("     n+1 := Insert_t n n.)")
    print()
    print("Stage 3A (b) -- IS_TERM_NUMERAL.")
    print("    IS_TERM_EMPTY    :", pp_thm(IS_TERM_EMPTY))
    print("    IS_TERM_INSERT   :", pp_thm(IS_TERM_INSERT))
    print("    IS_TERM_NUMERAL  :", pp_thm(IS_TERM_NUMERAL))
    print()
    print("Stage 3B (set-native target) -- dependency-set HF proof objects.")
    print("    VALID_STEP_HF_SET_DEF       :", pp_thm(VALID_STEP_HF_SET_DEF))
    print("    VALID_STEP_HF_SET_AT        :", pp_thm(VALID_STEP_HF_SET_AT))
    print("    PROOF_HF_SET_DEF            :", pp_thm(PROOF_HF_SET_DEF))
    print("    PROOF_HF_SET_AT             :", pp_thm(PROOF_HF_SET_AT))
    print("    VALID_STEP_HF_SET_PRESERVES :", pp_thm(VALID_STEP_HF_SET_PRESERVES))
    print("    AXIOM_HAS_PROOF_HF_SET      :", pp_thm(AXIOM_HAS_PROOF_HF_SET))
    print("    MP_HAS_PROOF_HF_SET         :", pp_thm(MP_HAS_PROOF_HF_SET))
    print("    GEN_HAS_PROOF_HF_SET        :", pp_thm(GEN_HAS_PROOF_HF_SET))
    print()
    print("Stage 3B (j-l) -- set-native Sigma_1 Prov_HF and closure rules.")
    print("    PROV_HF_DEF         :", pp_thm(PROV_HF_DEF))
    print("    PROV_HF_AT          :", pp_thm(PROV_HF_AT))
    print("    PROV_HF_AXIOM       :", pp_thm(PROV_HF_AXIOM))
    print("    PROV_HF_MP          :", pp_thm(PROV_HF_MP))
    print("    PROV_HF_GEN         :", pp_thm(PROV_HF_GEN))
    print("    PROV_HF_IFF_PROOF_HF_SET :", pp_thm(PROV_HF_IFF_PROOF_HF_SET))
    print()
    print("Stage 3B (m) -- representability scaffolding.")
    print("    REPRESENTS_PRED_DEF :", pp_thm(REPRESENTS_PRED_DEF))
    print("    REPRESENTS_PRED_AT  :", pp_thm(REPRESENTS_PRED_AT))
    print()
    print("Stage 3C (a) -- representability of substitute.")
    print("    VAR_Z_DEF              :", pp_thm(VAR_Z_DEF))
    print("    VAR_W_DEF              :", pp_thm(VAR_W_DEF))
    print("    VAR_T_DEF              :", pp_thm(VAR_T_DEF))
    print("    VAR_A_DEF              :", pp_thm(VAR_A_DEF))
    print("    VAR_B_DEF              :", pp_thm(VAR_B_DEF))
    print("    VAR_S1_DEF              :", pp_thm(VAR_S1_DEF))
    print("    VAR_S2_DEF              :", pp_thm(VAR_S2_DEF))
    print("    VAR_WQ_DEF             :", pp_thm(VAR_WQ_DEF))
    print("    VAR_A1_DEF              :", pp_thm(VAR_A1_DEF))
    print("    VAR_A2_DEF              :", pp_thm(VAR_A2_DEF))
    print("    VAR_B1_DEF              :", pp_thm(VAR_B1_DEF))
    print("    VAR_B2_DEF              :", pp_thm(VAR_B2_DEF))
    print("    VAR_F1_DEF              :", pp_thm(VAR_F1_DEF))
    print("    VAR_F2_DEF              :", pp_thm(VAR_F2_DEF))
    print("    HF_SUPPORT_PREDICATE_PACKAGE          :", pp_thm(HF_SUPPORT_PREDICATE_PACKAGE))
    print("    IS_TERM_INTERNAL_REPRESENTS           :", pp_thm(IS_TERM_INTERNAL_REPRESENTS))
    print("    NOT_IS_TERM_INTERNAL_REPRESENTS       :", pp_thm(NOT_IS_TERM_INTERNAL_REPRESENTS))
    print("    IS_FORM_INTERNAL_REPRESENTS           :", pp_thm(IS_FORM_INTERNAL_REPRESENTS))
    print("    NOT_IS_FORM_INTERNAL_REPRESENTS       :", pp_thm(NOT_IS_FORM_INTERNAL_REPRESENTS))
    print("    FREE_IN_INTERNAL_REPRESENTS           :", pp_thm(FREE_IN_INTERNAL_REPRESENTS))
    print("    NOT_FREE_IN_INTERNAL_REPRESENTS       :", pp_thm(NOT_FREE_IN_INTERNAL_REPRESENTS))
    print("    HF_SYNTAX_REC_PACKAGE                 :", pp_thm(HF_SYNTAX_REC_PACKAGE))
    print("    SUBSTITUTE_REPRESENTS_SYNTACTIC       :", pp_thm(SUBSTITUTE_REPRESENTS_SYNTACTIC))
    print("    SUBSTITUTE_REPRESENTS_TERM            :", pp_thm(SUBSTITUTE_REPRESENTS_TERM))
    print("    SUBSTITUTE_REPRESENTS_FORM            :", pp_thm(SUBSTITUTE_REPRESENTS_FORM))
    print("    TEMPLATE_FILL_EMPTY                   :", pp_thm(TEMPLATE_FILL_EMPTY))
    print("    TEMPLATE_FILL_HOLE_HIT                :", pp_thm(TEMPLATE_FILL_HOLE_HIT))
    print("    TEMPLATE_FILL_HOLE_MISS               :", pp_thm(TEMPLATE_FILL_HOLE_MISS))
    print("    TEMPLATE_FILL_INSERT                  :", pp_thm(TEMPLATE_FILL_INSERT))
    print("    TEMPLATE_FILL_QPARSE_VAR_T            :", pp_thm(TEMPLATE_FILL_QPARSE_VAR_T))
    print("    TEMPLATE_FILL_REPRESENTS_TERM         :", pp_thm(TEMPLATE_FILL_REPRESENTS_TERM))
    print("    QUOTE_HF_AT_EMPTY                    :", pp_thm(QUOTE_HF_AT_EMPTY))
    print("    QUOTE_HF_AT_INSERT_LOW               :", pp_thm(QUOTE_HF_AT_INSERT_LOW))
    print("    QUOTE_HF_AT_SINGLETON                :", pp_thm(QUOTE_HF_AT_SINGLETON))
    print("    QUOTE_HF_AT_PAIR                      :", pp_thm(QUOTE_HF_AT_PAIR))
    print("    QUOTE_HF_AT_PAIR_ORD                  :", pp_thm(QUOTE_HF_AT_PAIR_ORD))
    print("    HF_INDUCTION                          :", pp_thm(HF_INDUCTION))
    print("    IS_TERM_QUOTE_HF                      :", pp_thm(IS_TERM_QUOTE_HF))
    print("    SUBSTITUTE_QUOTE_HF                   :", pp_thm(SUBSTITUTE_QUOTE_HF))
    print("    IS_PAIR_ORD_INTERNAL_DEF              :", pp_thm(IS_PAIR_ORD_INTERNAL_DEF))
    print("    PROV_HF_REFL                          :", pp_thm(PROV_HF_REFL))
    print("    IS_PAIR_ORD_REPRESENTS                :", pp_thm(IS_PAIR_ORD_REPRESENTS))
    print()
    print(
        "    (Stage 3 high-layer reps -- QUOTE_HF_MEM_DECISION,",
        "PROV_HF_REPRESENTS,",
    )
    print("     IS_FORM_PROV_HF_INTERNAL, FREE_IN_PROV_HF_INTERNAL")
    print("     -- live in hf_repr_thms.py.)")
    print()
    print("Stage 3D (a) -- substitute_2 helper (used by diagonal lemma).")
    print("    SUBSTITUTE_2_DEF        :", pp_thm(SUBSTITUTE_2_DEF))
