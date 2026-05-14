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
# This file still contains the older list-based ``Proof_HF`` scaffolding
# as legacy external code. The active provability route is ranked finite
# HF-set proof objects via ``Proof_HF_set``; ``Prov_HF`` is defined from
# that predicate, not from lists.
#

from fusion import Var
from basics import mk_const, mk_app, mk_abs, rand, rator
from parser import define, parse_type
from axioms import mk_forall, mk_imp, mk_not, mk_and, mk_or, mk_exists
from nat0 import nat0_ty, define_unary_0, mk_suc0, ZERO, AXIOM_3_0, AXIOM_4_0
from nat0_order import define_wf_lt
from proof import proof, define_with_at
from tactics import (
    SPEC,
    SPECL,
    GEN,
    GENL,
    SYM,
    AP_THM,
    BETA_CONV,
    TRANS,
    DISJ1,
    DISJ2,
    REFL,
    EQ_MP,
    MP,
    CONJ,
    CONJUNCT1,
    CONJUNCT2,
    EXISTS,
    NOT_INTRO,
    DISCH,
    NOT_ELIM,
    EQF_INTRO,
    CONTR,
    DISJ_CASES,
)
from axioms import F
from fusion import ASSUME, ABS
from basics import mk_eq

from hf_syntax import (
    Var_t,  # noqa: F401  -- parser alias for is_substitute_step
    Eq_f,  # noqa: F401  -- parser alias for is_substitute_step
    Not_f,  # noqa: F401  -- parser alias for is_substitute_step
    Imp_f,  # noqa: F401  -- parser alias for is_substitute_step
    Forall_f,  # noqa: F401  -- parser alias for is_substitute_step
    Insert_t,
    Empty_t,
    In_a,  # noqa: F401  -- parser alias for is_substitute_step
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
    mono_iff_eq_or_pw_step,
    _unfold_rec_via_F_def,
    _extract_nfg,
    _mono_iff_value_binary_pw_step,
)
from hf_sets import (
    In,  # noqa: F401  -- parser alias for is_substitute_step
    Pair_ord,  # noqa: F401  -- parser alias for is_substitute_step
    Insert,  # noqa: F401  -- parser alias for quote_hf bridge
    Empty,  # noqa: F401  -- parser alias for quote_hf bridge
    Singleton,  # noqa: F401  -- parser alias for QUOTE_HF_AT_SINGLETON
    Pair,  # noqa: F401  -- parser alias for QUOTE_HF_AT_PAIR
    Pair_ord,  # noqa: F401  -- parser alias for QUOTE_HF_AT_PAIR_ORD
    Union,  # used by TRACE_EXISTS to merge sub-traces
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
from axioms import mk_select
from axioms import dest_exists
from tactics import (
    CHOOSE_WITNESS,
    AP_TERM,
    OR_CONG,
    REWRITE_RULE,
)
from fusion import vsubst, aty, DEDUCT_ANTISYM_RULE, new_constant
from hf_proof import (
    var_x,
    VAR_X_DEF,
    var_y,
    VAR_Y_DEF,
    var_z,
    VAR_Z_DEF,
    nil_l,
    cons_l,
    CONS_L_INJ,
    CONS_L_NEQ_NIL,
    NAT0_LT_CONS_L_TAIL,
    is_axiom,
    is_hf_axiom,
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
# Stage 3A (c) -- shared constants and helpers used by the Stage 3B
# Proof_HF infrastructure and beyond.
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
# Stage 3B (set-native target) -- ranked HF-set proof objects.
#
# This is the intended representation for ``Prov_HF_internal``. A proof
# object ``P`` is a finite HF set of records ``Pair_ord k h`` where ``k``
# is the step rank and ``h`` is the formula proved at that rank. A record
# at rank ``k`` may cite only records with lower ranks. This keeps the
# object-language proof predicate set-native while preserving the
# well-founded "earlier proof step" discipline of Hilbert proofs.
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
    "      /\\ nat0_lt i k /\\ nat0_lt j k /\\ is_mp f g h) "
    "\\/ (?i f. In (Pair_ord i f) P /\\ nat0_lt i k /\\ is_gen f h)",
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
# Stage 3B (a) -- legacy external list membership ``mem_l``.
#
# NOTE: this list-based proof infrastructure is no longer the intended
# HF-internal representation of proofs. ``Prov_HF_internal`` should use
# HF-native proof objects (ranked finite sets / proof trees), so HF does
# not have to internalise ``cons_l`` list theory. The code below remains
# legacy external scaffolding and is not part of the ``Prov_HF`` route.
#
#   mem_l p x  :<=>  ?h t. p = cons_l h t /\ (x = h \/ mem_l t x).
#
# The nil_l case (``p = 0``) returns F naturally: there is no h, t such
# that ``nil_l = cons_l h t`` (CONS_L_NEQ_NIL). Recursion is on the
# first argument (the list), so ``mem_l : nat0 -> nat0 -> bool`` is
# declared via ``define_wf_lt`` with the body packaged into a helper
# constant ``_mem_l_F``. The MONO obligation is dispatched pointwise
# via ``mono_iff_eq_or_pw_step`` (matches ``(x = h \/ f t x)`` rest).
# ---------------------------------------------------------------------------


_pred2_ty = parse_type("nat0 -> nat0 -> bool")
_F_pred2_ty = parse_type("(nat0 -> nat0 -> bool) -> nat0 -> nat0 -> bool")
_f_pred2 = Var("f", _pred2_ty)
_p_n0_var = Var("p", nat0_ty)
_h_n0_local = Var("h", nat0_ty)
_t_n0_local = Var("t", nat0_ty)
_x_n0_for_mem = Var("x", nat0_ty)


def _mem_l_body(f_t, p_t, x_t):
    """Bool body of ``_mem_l_F`` at the x-applied level."""
    return mk_exists(
        _h_n0_local,
        mk_exists(
            _t_n0_local,
            mk_and(
                mk_eq(p_t, mk_app(cons_l, _h_n0_local, _t_n0_local)),
                mk_or(mk_eq(x_t, _h_n0_local), mk_app(f_t, _t_n0_local, x_t)),
            ),
        ),
    )


_MEM_L_F_DEF = define(
    "_mem_l_F",
    _F_pred2_ty,
    mk_abs(
        _f_pred2,
        mk_abs(
            _p_n0_var,
            mk_abs(_x_n0_for_mem, _mem_l_body(_f_pred2, _p_n0_var, _x_n0_for_mem)),
        ),
    ),
)
_MEM_L_F = mk_const("_mem_l_F", [])


@proof
def MEM_L_MONO(p):
    """|- !f g p. (!k. nat0_lt k p ==> f k = g k)
                  ==> _mem_l_F f p = _mem_l_F g p.

    Function-valued MONO: prove the bool body equation pointwise at a
    fixed ``x``, then ABS over x to lift to the lambda equality, then
    ``by_unfold`` through ``_MEM_L_F_DEF`` on each side."""
    p.goal(
        "!f g p. (!k. nat0_lt k p ==> f k = g k) ==> _mem_l_F f p = _mem_l_F g p",
        types={"f": _pred2_ty, "g": _pred2_ty, "p": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g p")
    p.assume("h: !k. nat0_lt k p ==> f k = g k")

    h_th = p.fact("h")
    body_eq = mono_iff_eq_or_pw_step(cons_l, NAT0_LT_CONS_L_TAIL, h_th, _x_n0_for_mem)
    # body_eq : {h_concl} |- body[f, p, x] = body[g, p, x].
    abs_eq = ABS(_x_n0_for_mem, body_eq)
    # abs_eq : {h_concl} |- (\x. body[f, p, x]) = (\x. body[g, p, x]).

    p.thus("_mem_l_F f p = _mem_l_F g p").by_unfold(abs_eq, _MEM_L_F_DEF)


MEM_L_DEF, _MEM_L_REC_RAW = define_wf_lt(
    "mem_l",
    _pred2_ty,
    _MEM_L_F,
    MEM_L_MONO,
)
mem_l = mk_const("mem_l", [])


# |- !p. mem_l p = (\x. ?h t. p = cons_l h t /\ (x = h \/ mem_l t x)).
MEM_L_REC = _unfold_rec_via_F_def(_MEM_L_REC_RAW, _MEM_L_F_DEF)


# Pointwise unfold:
#   |- !p x. mem_l p x = (?h t. p = cons_l h t /\ (x = h \/ mem_l t x)).
def _mem_l_rec_pw():
    spec_p = SPEC(_p_n0_var, MEM_L_REC)  # |- mem_l p = \x. body
    ap_x = AP_THM(spec_p, _x_n0_for_mem)  # |- mem_l p x = (\x. body) x
    rhs = rand(ap_x._concl)
    beta_x = BETA_CONV(rhs)  # |- (\x. body) x = body[x]
    pw = TRANS(ap_x, beta_x)  # |- mem_l p x = body[x]
    return GENL([_p_n0_var, _x_n0_for_mem], pw)


MEM_L_REC_PW = _mem_l_rec_pw()


# Constructor equations: nil_l and cons_l.
#
#   |- !x. mem_l nil_l x = F.
#   |- !h t x. mem_l (cons_l h t) x =
#              (x = h \/ mem_l t x).


_MEM_L_RHS_STR = "?h t. nil_l = cons_l h t /\\ (x = h \\/ mem_l t x)"


@proof
def MEM_L_AT_NIL(p):
    """|- !x. mem_l nil_l x = F."""
    p.goal("!x. mem_l nil_l x = F")
    p.fix("x")

    rec_at_nil_x = SPECL([p._parse("nil_l"), p._parse("x")], MEM_L_REC_PW)
    # rec_at_nil_x : |- mem_l nil_l x =
    #                  (?h t. nil_l = cons_l h t /\ (x = h \/ mem_l t x))

    # Show RHS = F via ~RHS:
    with p.have(f"rhs_neg: ~({_MEM_L_RHS_STR})").proof():
        with p.suppose(f"hex: {_MEM_L_RHS_STR}"):
            p.choose("h", "hex", eq_label="ex_t")
            p.choose("t", "ex_t", eq_label="conj_ht")
            p.split("conj_ht", "(eq_nil, _disj)")
            p.have("eq_swap: cons_l h t = nil_l").by_thm(SYM(p.fact("eq_nil")))
            p.have("neq: ~(cons_l h t = nil_l)").by(CONS_L_NEQ_NIL, "h", "t")
            p.absurd().by_conj("neq", "eq_swap")

    p.have(f"rhs_F: ({_MEM_L_RHS_STR}) = F").by_thm(EQF_INTRO(p.fact("rhs_neg")))
    p.thus("mem_l nil_l x = F").by_thm(TRANS(rec_at_nil_x, p.fact("rhs_F")))


@proof
def MEM_L_AT_CONS(p):
    """|- !h t x. mem_l (cons_l h t) x = (x = h \\/ mem_l t x)."""
    p.goal("!h t x. mem_l (cons_l h t) x = (x = h \\/ mem_l t x)")
    p.fix("h t x")

    rec_at = SPECL([p._parse("cons_l h t"), p._parse("x")], MEM_L_REC_PW)
    # rec_at : |- mem_l (cons_l h t) x =
    #            (?h1 t1. cons_l h t = cons_l h1 t1
    #                     /\ (x = h1 \/ mem_l t1 x))

    rhs_str = "?h1 t1. cons_l h t = cons_l h1 t1 /\\ (x = h1 \\/ mem_l t1 x)"
    target_str = "x = h \\/ mem_l t x"

    # Forward: RHS ==> target.
    with p.have(f"fwd: ({rhs_str}) ==> ({target_str})").proof():
        p.assume(f"hex: {rhs_str}")
        p.choose("h1", "hex", eq_label="ex_t")
        p.choose("t1", "ex_t", eq_label="conj")
        p.split("conj", "(eq_cons, disj)")
        p.have("inj: h = h1 /\\ t = t1").by(CONS_L_INJ, "h", "t", "h1", "t1", "eq_cons")
        p.split("inj", "(eq_h, eq_t)")
        # disj: x = h1 \/ mem_l t1 x; rewrite via SYM(eq_h), SYM(eq_t)
        # to land at: x = h \/ mem_l t x.
        p.thus(target_str).by_rewrite_of(
            "disj", [SYM(p.fact("eq_h")), SYM(p.fact("eq_t"))]
        )

    # Backward: target ==> RHS. Build the witness manually via EXISTS
    # so we don't have to coax REWRITE_PROVE through a disjunction.
    with p.have(f"rev: ({target_str}) ==> ({rhs_str})").proof():
        p.assume(f"htgt: {target_str}")
        h_t = p._parse("h")
        t_t = p._parse("t")
        x_t = p._parse("x")
        h1_var = Var("h1", nat0_ty)
        t1_var = Var("t1", nat0_ty)
        cons_h_t = mk_app(cons_l, h_t, t_t)
        body_th = CONJ(REFL(cons_h_t), p.fact("htgt"))
        # Inner pred: \t1. cons_l h t = cons_l h t1 /\ (x = h \/ mem_l t1 x)
        inner_body_t1 = mk_and(
            mk_eq(cons_h_t, mk_app(cons_l, h_t, t1_var)),
            mk_or(mk_eq(x_t, h_t), mk_app(mem_l, t1_var, x_t)),
        )
        inner_pred = mk_abs(t1_var, inner_body_t1)
        inner_th = EXISTS(inner_pred, t_t, body_th)
        # Outer pred: \h1. ?t1. cons_l h t = cons_l h1 t1
        #                       /\ (x = h1 \/ mem_l t1 x)
        outer_inner_body = mk_and(
            mk_eq(cons_h_t, mk_app(cons_l, h1_var, t1_var)),
            mk_or(mk_eq(x_t, h1_var), mk_app(mem_l, t1_var, x_t)),
        )
        outer_pred = mk_abs(h1_var, mk_exists(t1_var, outer_inner_body))
        outer_th = EXISTS(outer_pred, h_t, inner_th)
        p.thus(rhs_str).by_thm(outer_th)

    p.have(f"iff: ({rhs_str}) = ({target_str})").by_iff("fwd", "rev")
    p.thus("mem_l (cons_l h t) x = (x = h \\/ mem_l t x)").by_thm(
        TRANS(rec_at, p.fact("iff"))
    )


# ---------------------------------------------------------------------------
# Stage 3B (b) -- ``valid_step``: per-step proof checker.
#
#   valid_step t h  :<=>  is_axiom h
#                          \/ (?f1 f2. mem_l f1 t /\ mem_l f2 t /\
#                                       is_mp f1 f2 h)
#                          \/ (?f1. mem_l f1 t /\ is_gen f1 h)
#
# t is the tail (the formulas listed before h in the proof); h is
# justified as an axiom, by MP from two earlier formulas, or by Gen
# from one. Non-recursive in the sequence type, so plain ``define``.
# ---------------------------------------------------------------------------


_t_n0_vs = Var("t", nat0_ty)
_h_n0_vs = Var("h", nat0_ty)
_f1_n0_vs = Var("f1", nat0_ty)
_f2_n0_vs = Var("f2", nat0_ty)


_valid_step_body = mk_or(
    mk_app(is_axiom, _h_n0_vs),
    mk_or(
        mk_exists(
            _f1_n0_vs,
            mk_exists(
                _f2_n0_vs,
                mk_and(
                    mk_app(mem_l, _t_n0_vs, _f1_n0_vs),
                    mk_and(
                        mk_app(mem_l, _t_n0_vs, _f2_n0_vs),
                        mk_app(is_mp, _f1_n0_vs, _f2_n0_vs, _h_n0_vs),
                    ),
                ),
            ),
        ),
        mk_exists(
            _f1_n0_vs,
            mk_and(
                mk_app(mem_l, _t_n0_vs, _f1_n0_vs),
                mk_app(is_gen, _f1_n0_vs, _h_n0_vs),
            ),
        ),
    ),
)


# Pointwise:
#   |- !t h. valid_step t h =
#            (is_axiom h
#             \/ (?f1 f2. mem_l t f1 /\ mem_l t f2 /\ is_mp f1 f2 h)
#             \/ (?f1. mem_l t f1 /\ is_gen f1 h)).
VALID_STEP_DEF, VALID_STEP_AT = define_with_at(
    "valid_step",
    parse_type("nat0 -> nat0 -> bool"),
    mk_abs(_t_n0_vs, mk_abs(_h_n0_vs, _valid_step_body)),
)
valid_step = mk_const("valid_step", [])


# ---------------------------------------------------------------------------
# Stage 3B (c) -- list-based provability ``Proof_HF``.
#
#   Proof_HF p n  :<=>
#       ?h t. p = cons_l h t /\ h = n /\ valid_step t h /\
#             (t = nil_l \/ ?h_inner. Proof_HF t h_inner).
#
# A non-empty list ``p`` whose head ``h`` equals ``n``, every prefix is
# justified by ``valid_step`` against its tail, and (via the inner
# disjunction) the tail itself extends to a valid proof or is empty.
# When ``p = nil_l`` the body is F (no h, t with nil_l = cons_l h t,
# CONS_L_NEQ_NIL).
#
# Recursion target type is ``nat0 -> bool`` (Proof_HF : nat0 -> nat0 ->
# bool, recursing on the proof list). MONO obligation: pointwise body
# equation under fixed n, then ``ABS`` over n and ``by_unfold`` through
# the helper-constant DEF. The recursive call ``f t h_inner`` is buried
# under an inner ``?h_inner.`` existential under the disjunction; we
# rebuild that existential's iff by ``AP_THM`` + ``ABS`` + ``AP_TERM``
# at the existential constant ``?``.
# ---------------------------------------------------------------------------


_h_n0_pq = Var("h", nat0_ty)
_t_n0_pq = Var("t", nat0_ty)
_h_inner_pq = Var("h_inner", nat0_ty)
_n_n0_pq = Var("n", nat0_ty)


def _proof_q_body(f_t, p_t, n_t):
    """Bool body of ``_proof_q_F`` at the n-applied level."""
    return mk_exists(
        _h_n0_pq,
        mk_exists(
            _t_n0_pq,
            mk_and(
                mk_eq(p_t, mk_app(cons_l, _h_n0_pq, _t_n0_pq)),
                mk_and(
                    mk_eq(_h_n0_pq, n_t),
                    mk_and(
                        mk_app(valid_step, _t_n0_pq, _h_n0_pq),
                        mk_or(
                            mk_eq(_t_n0_pq, nil_l),
                            mk_exists(_h_inner_pq, mk_app(f_t, _t_n0_pq, _h_inner_pq)),
                        ),
                    ),
                ),
            ),
        ),
    )


_PROOF_HF_F_DEF = define(
    "_proof_q_F",
    _F_pred2_ty,
    mk_abs(
        _f_pred2,
        mk_abs(
            _p_n0_var, mk_abs(_n_n0_pq, _proof_q_body(_f_pred2, _p_n0_var, _n_n0_pq))
        ),
    ),
)
_PROOF_HF_F = mk_const("_proof_q_F", [])


def _proof_q_mono_body_iff(hyp_th, n_term):
    """|- (?h t. p = cons_l h t /\\ h = n /\\ valid_step t h /\\
                  (t = nil_l \\/ ?h_inner. f t h_inner))
        = (same with g)
    given ``hyp_th : |- !k. nat0_lt k p ==> f k = g k``.
    """
    p_t, f_t, g_t, _ = _extract_nfg(hyp_th)

    def _bodies(fn):
        return mk_and(
            mk_eq(p_t, mk_app(cons_l, _h_n0_pq, _t_n0_pq)),
            mk_and(
                mk_eq(_h_n0_pq, n_term),
                mk_and(
                    mk_app(valid_step, _t_n0_pq, _h_n0_pq),
                    mk_or(
                        mk_eq(_t_n0_pq, nil_l),
                        mk_exists(_h_inner_pq, mk_app(fn, _t_n0_pq, _h_inner_pq)),
                    ),
                ),
            ),
        )

    body_inner_l = _bodies(f_t)
    body_inner_r = _bodies(g_t)
    LHS = mk_exists(_h_n0_pq, mk_exists(_t_n0_pq, body_inner_l))
    RHS = mk_exists(_h_n0_pq, mk_exists(_t_n0_pq, body_inner_r))

    exists_const_n0 = mk_const("?", [(nat0_ty, aty)])

    def _direction(src, target_inner_body, swap_fg):
        h_top = ASSUME(src)
        outer_pred = dest_exists(src)
        chosen_outer = CHOOSE_WITNESS(outer_pred, h_top)
        new_inner_pred = dest_exists(chosen_outer._concl)
        chosen_inner = CHOOSE_WITNESS(new_inner_pred, chosen_outer)

        n_eq_th = CONJUNCT1(chosen_inner)
        rest1 = CONJUNCT2(chosen_inner)
        h_eq_n_th = CONJUNCT1(rest1)
        rest2 = CONJUNCT2(rest1)
        valid_th = CONJUNCT1(rest2)
        disj_th = CONJUNCT2(rest2)

        ctor_app = rand(n_eq_th._concl)
        wt = rand(ctor_app)
        wh = rand(rator(ctor_app))

        sl_t = SPEC(wt, SPEC(wh, NAT0_LT_CONS_L_TAIL))
        lt_t_p = REWRITE_RULE([SYM(n_eq_th)], sl_t)
        funcs_eq = MP(SPEC(wt, hyp_th), lt_t_p)
        funcs_eq_dir = SYM(funcs_eq) if swap_fg else funcs_eq

        funcs_at_h = AP_THM(funcs_eq_dir, _h_inner_pq)
        abs_eq = ABS(_h_inner_pq, funcs_at_h)
        inner_exists_eq = AP_TERM(exists_const_n0, abs_eq)

        wt_eq_nil = mk_eq(wt, nil_l)
        disj_eq = OR_CONG(REFL(wt_eq_nil), inner_exists_eq)
        new_disj_th = EQ_MP(disj_eq, disj_th)

        new_body = CONJ(n_eq_th, CONJ(h_eq_n_th, CONJ(valid_th, new_disj_th)))

        inner_pred_at_wh = mk_abs(_t_n0_pq, vsubst([(wh, _h_n0_pq)])(target_inner_body))
        inner_th = EXISTS(inner_pred_at_wh, wt, new_body)
        outer_pred_body = mk_abs(_h_n0_pq, mk_exists(_t_n0_pq, target_inner_body))
        outer_th = EXISTS(outer_pred_body, wh, inner_th)
        return outer_th

    R_th = _direction(LHS, body_inner_r, swap_fg=False)
    L_th = _direction(RHS, body_inner_l, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


@proof
def PROOF_HF_MONO(p):
    """|- !f g p. (!k. nat0_lt k p ==> f k = g k)
    ==> _proof_q_F f p = _proof_q_F g p."""
    p.goal(
        "!f g p. (!k. nat0_lt k p ==> f k = g k) ==> _proof_q_F f p = _proof_q_F g p",
        types={"f": _pred2_ty, "g": _pred2_ty, "p": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g p")
    p.assume("hyp: !k. nat0_lt k p ==> f k = g k")

    body_eq = _proof_q_mono_body_iff(p.fact("hyp"), _n_n0_pq)
    abs_eq = ABS(_n_n0_pq, body_eq)
    p.thus("_proof_q_F f p = _proof_q_F g p").by_unfold(abs_eq, _PROOF_HF_F_DEF)


PROOF_HF_DEF, _PROOF_HF_REC_RAW = define_wf_lt(
    "Proof_HF",
    _pred2_ty,
    _PROOF_HF_F,
    PROOF_HF_MONO,
)
Proof_HF = mk_const("Proof_HF", [])


# |- !p. Proof_HF p =
#         (\n. ?h t. p = cons_l h t /\ h = n /\ valid_step t h
#                    /\ (t = nil_l \/ ?h_inner. Proof_HF t h_inner)).
PROOF_HF_REC = _unfold_rec_via_F_def(_PROOF_HF_REC_RAW, _PROOF_HF_F_DEF)


# Pointwise unfold:
#   |- !p n. Proof_HF p n =
#            (?h t. p = cons_l h t /\ h = n /\ valid_step t h
#                   /\ (t = nil_l \/ ?h_inner. Proof_HF t h_inner)).
def _proof_q_rec_pw():
    spec_p = SPEC(_p_n0_var, PROOF_HF_REC)
    ap_n = AP_THM(spec_p, _n_n0_pq)
    rhs = rand(ap_n._concl)
    beta_n = BETA_CONV(rhs)
    pw = TRANS(ap_n, beta_n)
    return GENL([_p_n0_var, _n_n0_pq], pw)


PROOF_HF_REC_PW = _proof_q_rec_pw()


# Constructor equations.
_PROOF_HF_RHS_NIL_STR = (
    "?h t. nil_l = cons_l h t /\\ h = n /\\ valid_step t h /\\ "
    "(t = nil_l \\/ ?h_inner. Proof_HF t h_inner)"
)


@proof
def PROOF_HF_AT_NIL(p):
    """|- !n. Proof_HF nil_l n = F."""
    p.goal("!n. Proof_HF nil_l n = F")
    p.fix("n")

    rec_at = SPECL([p._parse("nil_l"), p._parse("n")], PROOF_HF_REC_PW)

    with p.have(f"rhs_neg: ~({_PROOF_HF_RHS_NIL_STR})").proof():
        with p.suppose(f"hex: {_PROOF_HF_RHS_NIL_STR}"):
            p.choose("h", "hex", eq_label="ex_t")
            p.choose("t", "ex_t", eq_label="conj_ht")
            p.split("conj_ht", "(eq_nil, _rest)")
            p.have("eq_swap: cons_l h t = nil_l").by_thm(SYM(p.fact("eq_nil")))
            p.have("neq: ~(cons_l h t = nil_l)").by(CONS_L_NEQ_NIL, "h", "t")
            p.absurd().by_conj("neq", "eq_swap")

    p.have(f"rhs_F: ({_PROOF_HF_RHS_NIL_STR}) = F").by_thm(EQF_INTRO(p.fact("rhs_neg")))
    p.thus("Proof_HF nil_l n = F").by_thm(TRANS(rec_at, p.fact("rhs_F")))


@proof
def PROOF_HF_AT_CONS(p):
    """|- !h t n. Proof_HF (cons_l h t) n =
    (h = n /\\ valid_step t h
     /\\ (t = nil_l \\/ ?h_inner. Proof_HF t h_inner))."""
    p.goal(
        "!h t n. Proof_HF (cons_l h t) n = "
        "(h = n /\\ valid_step t h "
        "/\\ (t = nil_l \\/ ?h_inner. Proof_HF t h_inner))"
    )
    p.fix("h t n")

    rec_at = SPECL([p._parse("cons_l h t"), p._parse("n")], PROOF_HF_REC_PW)
    rhs_str = (
        "?h1 t1. cons_l h t = cons_l h1 t1 /\\ h1 = n /\\ "
        "valid_step t1 h1 /\\ "
        "(t1 = nil_l \\/ ?h_inner. Proof_HF t1 h_inner)"
    )
    target_str = (
        "h = n /\\ valid_step t h /\\ (t = nil_l \\/ ?h_inner. Proof_HF t h_inner)"
    )

    # Forward: RHS ==> target.
    #
    # The disjunction inner-existential (?h_inner. Proof_HF t1 h_inner)
    # cannot be rewritten via ``by_rewrite_of`` on the whole disjunction
    # because the eq_t rule has non-empty asl (chained from ``hex``)
    # and the rewrite engine filters such rules under binders. Split
    # the disjunction by cases instead -- each case's rewrite happens
    # at the top level after CHOOSE.
    with p.have(f"fwd: ({rhs_str}) ==> ({target_str})").proof():
        p.assume(f"hex: {rhs_str}")
        p.choose("h1", "hex", eq_label="ex_t")
        p.choose("t1", "ex_t", eq_label="conj")
        p.split("conj", "(eq_cons, h1_eq_n, valid_t1, disj_t1)")
        p.have("inj: h = h1 /\\ t = t1").by(CONS_L_INJ, "h", "t", "h1", "t1", "eq_cons")
        p.split("inj", "(eq_h, eq_t)")
        p.have("h_eq_n: h = n").by_rewrite_of("h1_eq_n", [SYM(p.fact("eq_h"))])
        p.have("valid_th: valid_step t h").by_rewrite_of(
            "valid_t1", [SYM(p.fact("eq_h")), SYM(p.fact("eq_t"))]
        )
        with p.have("disj_th: t = nil_l \\/ ?h_inner. Proof_HF t h_inner").proof():
            with p.cases_on("disj_t1"):
                with p.case("nil_c: t1 = nil_l"):
                    p.have("t_eq_nil: t = nil_l").by_rewrite_of(
                        "nil_c", [SYM(p.fact("eq_t"))]
                    )
                    p.thus("t = nil_l \\/ ?h_inner. Proof_HF t h_inner").by_disj(
                        "t_eq_nil"
                    )
                with p.case("ex_c: ?h_inner. Proof_HF t1 h_inner"):
                    # case auto-introduces ``h_inner`` witness with eq
                    # fact ``h_inner_eq: Proof_HF t1 h_inner``.
                    p.have("pq_at_t: Proof_HF t h_inner").by_rewrite_of(
                        "h_inner_eq", [SYM(p.fact("eq_t"))]
                    )
                    p.disj_witness("h_inner", "pq_at_t")
        p.thus(target_str).by_thm(
            CONJ(p.fact("h_eq_n"), CONJ(p.fact("valid_th"), p.fact("disj_th")))
        )

    # Backward: target ==> RHS.
    with p.have(f"rev: ({target_str}) ==> ({rhs_str})").proof():
        p.assume(f"htgt: {target_str}")
        p.split("htgt", "(h_eq_n, valid_th, disj_th)")

        h_t = p._parse("h")
        t_t = p._parse("t")
        n_t = p._parse("n")
        h1_var = Var("h1", nat0_ty)
        t1_var = Var("t1", nat0_ty)
        cons_h_t = mk_app(cons_l, h_t, t_t)

        body_th = CONJ(
            REFL(cons_h_t),
            CONJ(p.fact("h_eq_n"), CONJ(p.fact("valid_th"), p.fact("disj_th"))),
        )

        inner_body_t1 = mk_and(
            mk_eq(cons_h_t, mk_app(cons_l, h_t, t1_var)),
            mk_and(
                mk_eq(h_t, n_t),
                mk_and(
                    mk_app(valid_step, t1_var, h_t),
                    mk_or(
                        mk_eq(t1_var, nil_l),
                        mk_exists(_h_inner_pq, mk_app(Proof_HF, t1_var, _h_inner_pq)),
                    ),
                ),
            ),
        )
        inner_pred = mk_abs(t1_var, inner_body_t1)
        inner_th = EXISTS(inner_pred, t_t, body_th)

        outer_inner_body = mk_and(
            mk_eq(cons_h_t, mk_app(cons_l, h1_var, t1_var)),
            mk_and(
                mk_eq(h1_var, n_t),
                mk_and(
                    mk_app(valid_step, t1_var, h1_var),
                    mk_or(
                        mk_eq(t1_var, nil_l),
                        mk_exists(_h_inner_pq, mk_app(Proof_HF, t1_var, _h_inner_pq)),
                    ),
                ),
            ),
        )
        outer_pred = mk_abs(h1_var, mk_exists(t1_var, outer_inner_body))
        outer_th = EXISTS(outer_pred, h_t, inner_th)
        p.thus(rhs_str).by_thm(outer_th)

    p.have(f"iff: ({rhs_str}) = ({target_str})").by_iff("fwd", "rev")
    p.thus(
        "Proof_HF (cons_l h t) n = "
        "(h = n /\\ valid_step t h "
        "/\\ (t = nil_l \\/ ?h_inner. Proof_HF t h_inner))"
    ).by_thm(TRANS(rec_at, p.fact("iff")))


# ---------------------------------------------------------------------------
# Stage 3B (d) -- list concatenation ``append_l``.
#
#   append_l nil_l           q  =  q.
#   append_l (cons_l h t)    q  =  cons_l h (append_l t q).
#
# Recursion is on the first argument; the recursion target type is
# ``nat0 -> nat0`` (the post-q-curried function). Body is a SELECT over
# the result variable ``r``:
#
#   F f p  :=  \q. @r. (p = nil_l /\ r = q)
#                       \/ (?h t. p = cons_l h t
#                                  /\ r = cons_l h (f t q)).
#
# The MONO obligation reuses ``_mono_iff_value_binary_pw_step`` from
# ``hf_syntax`` for the cons disjunct (only the tail recurses, so
# ``recurses_l=False``, with size lemma ``NAT0_LT_CONS_L_TAIL``); the
# nil disjunct is non-recursive and falls through ``REFL``.
#
# Used in Stage 3B (e) to combine two proof-list witnesses (one ending
# at ``f``, one ending at ``Imp_f f g``) into a single longer list that
# witnesses ``Proof_HF``-derivability of ``g``: the ``Prov_HF ==> ?p.
# Proof_HF p n`` direction needs to verify the MP closure clause, which
# is precisely this combine step.
# ---------------------------------------------------------------------------


_pred_app_ty = parse_type("nat0 -> nat0 -> nat0")
_F_pred_app_ty = parse_type("(nat0 -> nat0 -> nat0) -> nat0 -> nat0 -> nat0")
_f_pred_app = Var("f", _pred_app_ty)
_p_n0_app = Var("p", nat0_ty)
_q_n0_app = Var("q", nat0_ty)
_r_n0_app = Var("r", nat0_ty)
_h_n0_app = Var("h", nat0_ty)
_t_n0_app = Var("t", nat0_ty)


def _append_l_inner_body(f_t, p_t, q_t, r_t):
    """Bool body inside the ``@r`` SELECT."""
    return mk_or(
        mk_and(mk_eq(p_t, nil_l), mk_eq(r_t, q_t)),
        mk_exists(
            _h_n0_app,
            mk_exists(
                _t_n0_app,
                mk_and(
                    mk_eq(p_t, mk_app(cons_l, _h_n0_app, _t_n0_app)),
                    mk_eq(r_t, mk_app(cons_l, _h_n0_app, mk_app(f_t, _t_n0_app, q_t))),
                ),
            ),
        ),
    )


_APPEND_L_F_DEF = define(
    "_append_l_F",
    _F_pred_app_ty,
    mk_abs(
        _f_pred_app,
        mk_abs(
            _p_n0_app,
            mk_abs(
                _q_n0_app,
                mk_select(
                    _r_n0_app,
                    _append_l_inner_body(_f_pred_app, _p_n0_app, _q_n0_app, _r_n0_app),
                ),
            ),
        ),
    ),
)
_APPEND_L_F = mk_const("_append_l_F", [])


@proof
def APPEND_L_MONO(p):
    """|- !f g p. (!k. nat0_lt k p ==> f k = g k)
                  ==> _append_l_F f p = _append_l_F g p.

    Two-disjunct body iff under the SELECT: nil disjunct is non-recursive
    (``REFL``); cons disjunct is binary-pw with ``recurses_l=False`` and
    ``rest_builder = (\\fn h t [q]. r = cons_l h (fn t q))``. ``OR_CONG``
    combines, then ``ABS r``, ``AP_TERM @``, ``ABS q``, ``by_unfold``."""
    p.goal(
        "!f g p. (!k. nat0_lt k p ==> f k = g k) ==> _append_l_F f p = _append_l_F g p",
        types={"f": _pred_app_ty, "g": _pred_app_ty, "p": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g p")
    p.assume("h: !k. nat0_lt k p ==> f k = g k")

    h_th = p.fact("h")

    # Nil disjunct: no recursion.
    p_t = p._parse("p")
    nil_disj_eq = REFL(mk_and(mk_eq(p_t, nil_l), mk_eq(_r_n0_app, _q_n0_app)))

    # Cons disjunct via the value-binary helper, recurses_l=False.
    cons_disj_eq = _mono_iff_value_binary_pw_step(
        cons_l,
        None,
        NAT0_LT_CONS_L_TAIL,
        h_th,
        [_q_n0_app],
        rest_builder=lambda fn, hh, tt, ags: mk_eq(
            _r_n0_app,
            mk_app(cons_l, hh, mk_app(fn, tt, *ags)),
        ),
        recurses_l=False,
    )

    body_eq = OR_CONG(nil_disj_eq, cons_disj_eq)
    # body_eq : {h_concl} |- body[f, p, q, r] = body[g, p, q, r]

    abs_r_eq = ABS(_r_n0_app, body_eq)
    sel_const = mk_const("@", [(nat0_ty, aty)])
    select_eq = AP_TERM(sel_const, abs_r_eq)
    abs_q_eq = ABS(_q_n0_app, select_eq)

    p.thus("_append_l_F f p = _append_l_F g p").by_unfold(abs_q_eq, _APPEND_L_F_DEF)


APPEND_L_DEF, _APPEND_L_REC_RAW = define_wf_lt(
    "append_l",
    _pred_app_ty,
    _APPEND_L_F,
    APPEND_L_MONO,
)
append_l = mk_const("append_l", [])


# |- !p. append_l p =
#         (\q. @r. (p = nil_l /\ r = q)
#                  \/ (?h t. p = cons_l h t
#                            /\ r = cons_l h (append_l t q))).
APPEND_L_REC = _unfold_rec_via_F_def(_APPEND_L_REC_RAW, _APPEND_L_F_DEF)


# Constructor recursion equations.


def _append_l_nil_body_iff(q_t):
    """|- (nil_l = nil_l /\\ r = q) \\/
          (?h t. nil_l = cons_l h t /\\ r = cons_l h (append_l t q))
        = (r = q).

    Built at kernel level: nil disjunct collapses (REFL nil_l makes the
    left conjunct T); cons disjunct is F (CONS_L_NEQ_NIL); OR_CONG
    chains them. Cleaner than going through the DSL because ``r`` is a
    free variable, not a fix-bound one.
    """
    r_t = _r_n0_app
    h_var = _h_n0_app
    t_var = _t_n0_app
    refl_nil = REFL(nil_l)
    nil_left = mk_eq(nil_l, nil_l)
    rq = mk_eq(r_t, q_t)
    nil_disj = mk_and(nil_left, rq)

    # nil_disj_iff : |- (nil_l = nil_l /\ r = q) = (r = q).
    fwd_n = DISCH(nil_disj, CONJUNCT2(ASSUME(nil_disj)))
    rev_n = DISCH(rq, CONJ(refl_nil, ASSUME(rq)))
    nil_disj_iff = DEDUCT_ANTISYM_RULE(
        MP(rev_n, ASSUME(rq)),
        MP(fwd_n, ASSUME(nil_disj)),
    )

    # cons_disj_iff : |- (?h t. nil_l = cons_l h t /\ ...) = F.
    cons_inner_body = mk_and(
        mk_eq(nil_l, mk_app(cons_l, h_var, t_var)),
        mk_eq(r_t, mk_app(cons_l, h_var, mk_app(append_l, t_var, q_t))),
    )
    cons_disj = mk_exists(h_var, mk_exists(t_var, cons_inner_body))

    # ~cons_disj.
    cons_assume = ASSUME(cons_disj)
    outer_pred = dest_exists(cons_disj)
    chosen_outer = CHOOSE_WITNESS(outer_pred, cons_assume)
    inner_pred = dest_exists(chosen_outer._concl)
    chosen_inner = CHOOSE_WITNESS(inner_pred, chosen_outer)
    eq_nil_th = CONJUNCT1(chosen_inner)
    # eq_nil_th : {cons_disj} |- nil_l = cons_l <wh> <wt>
    ctor_app = rand(eq_nil_th._concl)
    wt = rand(ctor_app)
    wh = rand(rator(ctor_app))
    swap_th = SYM(eq_nil_th)
    # swap_th : {cons_disj} |- cons_l wh wt = nil_l
    neq_th = SPEC(wt, SPEC(wh, CONS_L_NEQ_NIL))
    # neq_th : |- ~(cons_l wh wt = nil_l)
    F_th = MP(NOT_ELIM(neq_th), swap_th)
    # F_th : {cons_disj} |- F
    not_cons_disj = NOT_INTRO(DISCH(cons_disj, F_th))
    cons_disj_iff = SYM(EQF_INTRO(not_cons_disj))
    # cons_disj_iff : |- cons_disj = F  (EQF_INTRO returns F = p, hence SYM).

    # Combine: (nil_disj \/ cons_disj) = ((r = q) \/ F).
    or_iff = OR_CONG(nil_disj_iff, cons_disj_iff)
    # ((r = q) \/ F) = (r = q) via _build_or_F_right or manual.
    rq_or_F = mk_or(rq, F)
    # Manual: (X \/ F) = X.
    fwd_orF_imp = DISCH(rq_or_F, _disj_or_F_right(rq))
    rev_orF_imp = DISCH(rq, DISJ1(ASSUME(rq), F))
    orF_iff = DEDUCT_ANTISYM_RULE(
        MP(rev_orF_imp, ASSUME(rq)),
        MP(fwd_orF_imp, ASSUME(rq_or_F)),
    )
    return TRANS(or_iff, orF_iff)


def _disj_or_F_right(rq):
    """{rq \\/ F} |- rq."""
    rq_or_F = mk_or(rq, F)
    th_l = DISCH(rq, ASSUME(rq))  # |- rq ==> rq
    th_r = DISCH(F, CONTR(rq, ASSUME(F)))  # |- F ==> rq
    return DISJ_CASES(ASSUME(rq_or_F), th_l, th_r)


@proof
def APPEND_L_AT_NIL(p):
    """|- !q. append_l nil_l q = q."""
    p.goal("!q. append_l nil_l q = q")
    p.fix("q")

    q_t = p._parse("q")
    rec_at_nil = SPEC(p._parse("nil_l"), APPEND_L_REC)
    ap_q = AP_THM(rec_at_nil, q_t)
    body_at = TRANS(ap_q, BETA_CONV(rand(ap_q._concl)))
    # body_at : |- append_l nil_l q = (@r. body[nil_l, q, r])

    body_iff = _append_l_nil_body_iff(q_t)
    abs_eq = ABS(_r_n0_app, body_iff)
    sel_const = mk_const("@", [(nat0_ty, aty)])
    sel_eq = AP_TERM(sel_const, abs_eq)

    from hf_syntax import _select_collapse_eq

    collapse = _select_collapse_eq(q_t, _r_n0_app)
    full_eq = TRANS(body_at, TRANS(sel_eq, collapse))
    p.thus("append_l nil_l q = q").by_thm(full_eq)


def _append_l_cons_body_iff(h_t, t_t, q_t):
    """|- (cons_l h t = nil_l /\\ r = q) \\/
          (?h1 t1. cons_l h t = cons_l h1 t1
                    /\\ r = cons_l h1 (append_l t1 q))
        = (r = cons_l h (append_l t q)).

    Nil disjunct: F (CONS_L_NEQ_NIL). Cons disjunct: collapses to
    ``r = cons_l h (append_l t q)`` by injectivity.
    """
    r_t = _r_n0_app
    h1_var = Var("h1", nat0_ty)
    t1_var = Var("t1", nat0_ty)
    cons_h_t = mk_app(cons_l, h_t, t_t)
    target_K = mk_app(cons_l, h_t, mk_app(append_l, t_t, q_t))
    target_eq = mk_eq(r_t, target_K)

    nil_disj = mk_and(mk_eq(cons_h_t, nil_l), mk_eq(r_t, q_t))

    # nil_disj_iff : |- nil_disj = F.
    nil_assume = ASSUME(nil_disj)
    eq_nil_th = CONJUNCT1(nil_assume)
    neq_cht = SPEC(t_t, SPEC(h_t, CONS_L_NEQ_NIL))
    F_from_nil = MP(NOT_ELIM(neq_cht), eq_nil_th)
    not_nil_disj = NOT_INTRO(DISCH(nil_disj, F_from_nil))
    nil_disj_iff = SYM(EQF_INTRO(not_nil_disj))

    # cons_disj_iff : |- cons_disj = target_eq.
    cons_inner_body = mk_and(
        mk_eq(cons_h_t, mk_app(cons_l, h1_var, t1_var)),
        mk_eq(r_t, mk_app(cons_l, h1_var, mk_app(append_l, t1_var, q_t))),
    )
    cons_disj = mk_exists(h1_var, mk_exists(t1_var, cons_inner_body))

    # Forward: {cons_disj} |- target_eq.
    cons_assume = ASSUME(cons_disj)
    outer_pred = dest_exists(cons_disj)
    chosen_outer = CHOOSE_WITNESS(outer_pred, cons_assume)
    inner_pred = dest_exists(chosen_outer._concl)
    chosen_inner = CHOOSE_WITNESS(inner_pred, chosen_outer)
    eq_cons_th = CONJUNCT1(chosen_inner)
    eqr_th = CONJUNCT2(chosen_inner)
    # Witnesses: wh1, wt1 from eq_cons_th's RHS.
    rhs_ctor = rand(eq_cons_th._concl)
    wt1 = rand(rhs_ctor)
    wh1 = rand(rator(rhs_ctor))
    inj_th = MP(SPECL([h_t, t_t, wh1, wt1], CONS_L_INJ), eq_cons_th)
    eq_h_th = CONJUNCT1(inj_th)
    eq_t_th = CONJUNCT2(inj_th)
    # Rewrite eqr_th: r = cons_l wh1 (append_l wt1 q) using SYM(eq_h_th),
    # SYM(eq_t_th) to get r = cons_l h (append_l t q).
    fwd_th = REWRITE_RULE([SYM(eq_h_th), SYM(eq_t_th)], eqr_th)
    # fwd_th has assumption cons_disj (via chosen_inner chain).

    # Reverse: {target_eq} |- cons_disj. Witness h1 := h, t1 := t.
    target_assume = ASSUME(target_eq)
    body_at_h_t = CONJ(REFL(cons_h_t), target_assume)
    inner_pred_t1 = mk_abs(
        t1_var,
        mk_and(
            mk_eq(cons_h_t, mk_app(cons_l, h_t, t1_var)),
            mk_eq(r_t, mk_app(cons_l, h_t, mk_app(append_l, t1_var, q_t))),
        ),
    )
    inner_th = EXISTS(inner_pred_t1, t_t, body_at_h_t)
    outer_pred_h1 = mk_abs(h1_var, mk_exists(t1_var, cons_inner_body))
    rev_th = EXISTS(outer_pred_h1, h_t, inner_th)
    # rev_th : {target_eq} |- cons_disj.

    cons_disj_iff = DEDUCT_ANTISYM_RULE(rev_th, fwd_th)
    # cons_disj_iff : |- cons_disj = target_eq.

    # OR_CONG(nil_disj_iff, cons_disj_iff) gives:
    #   (nil_disj \/ cons_disj) = (F \/ target_eq).
    or_iff = OR_CONG(nil_disj_iff, cons_disj_iff)

    # (F \/ X) = X.
    F_or_X = mk_or(F, target_eq)
    th_l = DISCH(F, CONTR(target_eq, ASSUME(F)))
    th_r = DISCH(target_eq, ASSUME(target_eq))
    fwd_FX = DISJ_CASES(ASSUME(F_or_X), th_l, th_r)
    fwd_FX_imp = DISCH(F_or_X, fwd_FX)
    rev_FX_imp = DISCH(target_eq, DISJ2(F, ASSUME(target_eq)))
    F_or_iff = DEDUCT_ANTISYM_RULE(
        MP(rev_FX_imp, ASSUME(target_eq)),
        MP(fwd_FX_imp, ASSUME(F_or_X)),
    )
    # F_or_iff : |- (F \/ target_eq) = target_eq.
    return TRANS(or_iff, F_or_iff)


@proof
def APPEND_L_AT_CONS(p):
    """|- !h t q. append_l (cons_l h t) q = cons_l h (append_l t q)."""
    p.goal("!h t q. append_l (cons_l h t) q = cons_l h (append_l t q)")
    p.fix("h t q")

    h_t = p._parse("h")
    t_t = p._parse("t")
    q_t = p._parse("q")
    rec_at_cons = SPEC(mk_app(cons_l, h_t, t_t), APPEND_L_REC)
    ap_q = AP_THM(rec_at_cons, q_t)
    body_at = TRANS(ap_q, BETA_CONV(rand(ap_q._concl)))

    body_iff = _append_l_cons_body_iff(h_t, t_t, q_t)
    abs_eq = ABS(_r_n0_app, body_iff)
    sel_const = mk_const("@", [(nat0_ty, aty)])
    sel_eq = AP_TERM(sel_const, abs_eq)

    from hf_syntax import _select_collapse_eq

    target_K = mk_app(cons_l, h_t, mk_app(append_l, t_t, q_t))
    collapse = _select_collapse_eq(target_K, _r_n0_app)
    full_eq = TRANS(body_at, TRANS(sel_eq, collapse))
    p.thus("append_l (cons_l h t) q = cons_l h (append_l t q)").by_thm(full_eq)


# ---------------------------------------------------------------------------
# Stage 3B (e) -- membership preservation under append.
#
#   |- !p1 h1. Proof_HF p1 h1 ==>
#       !p2 f. (mem_l p1 f \/ mem_l p2 f) ==> mem_l (append_l p1 p2) f.
#
# In words: if ``p1`` is a HF-proof (so it has the cons-of-nil-terminated
# shape recursively) then every element of ``p1`` and of ``p2`` is an
# element of the concatenation. Strong induction on ``p1``: PROOF_HF_AT
# unpacks ``p1 = cons_l hd tl``; the recursion either bottoms out at
# ``tl = nil_l`` (where ``append_l nil_l p2 = p2`` directly) or proceeds
# with ``Proof_HF tl h_inner`` (where the IH applies at ``tl`` and the
# disjunction is preserved through the cons-front element).
#
# Encoding via a disjunction in the consequent dodges the OR-associativity
# obligation we'd otherwise meet trying to prove the iff form
# ``mem_l (append_l p1 p2) f = mem_l p1 f \/ mem_l p2 f``: the implication
# is what's actually needed at the use site (validity-step preservation
# in the MP closure), and there is no second direction to prove.
# ---------------------------------------------------------------------------


@proof
def MEM_L_APPEND_PRESERVES(p):
    """|- !p1 h1. Proof_HF p1 h1 ==>
    !p2 f. (mem_l p1 f \\/ mem_l p2 f)
           ==> mem_l (append_l p1 p2) f."""
    p.goal(
        "!p1. !h1. Proof_HF p1 h1 ==> "
        "!p2 f. (mem_l p1 f \\/ mem_l p2 f) "
        "==> mem_l (append_l p1 p2) f"
    )
    with p.strong_induction("p1", "IH"):
        p.fix("h1")
        p.assume("pq: Proof_HF p1 h1")
        p.fix("p2 f")
        p.assume("hd: mem_l p1 f \\/ mem_l p2 f")

        # Unfold pq to extract p1 = cons_l hd_v tl, hd_v = h1, etc.
        rec_pq = SPECL([p._parse("p1"), p._parse("h1")], PROOF_HF_REC_PW)
        body_str = (
            "?h t. p1 = cons_l h t /\\ h = h1 /\\ valid_step t h "
            "/\\ (t = nil_l \\/ ?h_inner. Proof_HF t h_inner)"
        )
        p.have(f"body: {body_str}").by_eq_mp(rec_pq, "pq")
        p.choose("hd_v", "body", eq_label="ex_t")
        p.choose("tl", "ex_t", eq_label="conj")
        p.split("conj", "(p_eq_cons, _hd_eq_h1, _valid, tail_disj)")

        # nat0_lt tl p1 (for the IH).
        lt_t_cons = SPECL([p._parse("hd_v"), p._parse("tl")], NAT0_LT_CONS_L_TAIL)
        p.have("lt_tl_p1: nat0_lt tl p1").by_rewrite_of(
            lt_t_cons, [SYM(p.fact("p_eq_cons"))]
        )

        # Compute append_l p1 p2 = cons_l hd_v (append_l tl p2).
        ap_at = SPECL(
            [p._parse("hd_v"), p._parse("tl"), p._parse("p2")],
            APPEND_L_AT_CONS,
        )
        # ap_at : append_l (cons_l hd_v tl) p2 = cons_l hd_v (append_l tl p2).
        p.have("app_eq: append_l p1 p2 = cons_l hd_v (append_l tl p2)").by_rewrite_of(
            ap_at, [SYM(p.fact("p_eq_cons"))]
        )

        # mem_l (cons_l hd_v (append_l tl p2)) f =
        #   (f = hd_v \/ mem_l (append_l tl p2) f).
        mem_cons_app = SPECL(
            [p._parse("hd_v"), p._parse("append_l tl p2"), p._parse("f")],
            MEM_L_AT_CONS,
        )
        # mem_l p1 f = (f = hd_v \/ mem_l tl f).
        mem_p1 = SPECL(
            [p._parse("hd_v"), p._parse("tl"), p._parse("f")],
            MEM_L_AT_CONS,
        )
        p.have("mem_at_p1: mem_l p1 f = (f = hd_v \\/ mem_l tl f)").by_rewrite_of(
            mem_p1, [SYM(p.fact("p_eq_cons"))]
        )

        # Step into cases on hd: f in p1 or f in p2.
        with p.cases_on("hd"):
            with p.case("from1: mem_l p1 f"):
                # from1 unfolds to f = hd_v \/ mem_l tl f.
                p.have("disj_p1: f = hd_v \\/ mem_l tl f").by_eq_mp(
                    p.fact("mem_at_p1"), "from1"
                )

                with p.cases_on("disj_p1"):
                    with p.case("ck_hd: f = hd_v"):
                        # mem_l (append_l p1 p2) f via head: cons_l hd_v _.
                        # Build mem_l (cons_l hd_v (append_l tl p2)) f
                        # via DISJ1 (f = hd_v) then EQ_MP SYM(mem_cons_app).
                        p.have(
                            "left_disj: f = hd_v \\/ mem_l (append_l tl p2) f"
                        ).by_disj("ck_hd")
                        p.have(
                            "mem_app_cons: mem_l (cons_l hd_v (append_l tl p2)) f"
                        ).by_eq_mp(SYM(mem_cons_app), "left_disj")
                        p.thus("mem_l (append_l p1 p2) f").by_rewrite_of(
                            "mem_app_cons", [SYM(p.fact("app_eq"))]
                        )
                    with p.case("mem_in_tl: mem_l tl f"):
                        # tl is nil or has Proof_HF; in nil case mem_l = F.
                        with p.cases_on("tail_disj"):
                            with p.case("tnil: tl = nil_l"):
                                p.have("mem_nil: mem_l nil_l f").by_rewrite_of(
                                    "mem_in_tl", [p.fact("tnil")]
                                )
                                mem_nil_at = SPEC(p._parse("f"), MEM_L_AT_NIL)
                                p.have("F_th: F").by_eq_mp(mem_nil_at, "mem_nil")
                                p.thus("mem_l (append_l p1 p2) f").by_thm(
                                    CONTR(
                                        p._parse("mem_l (append_l p1 p2) f"),
                                        p.fact("F_th"),
                                    )
                                )
                            with p.case("tex: ?h_inner. Proof_HF tl h_inner"):
                                # h_inner_eq: Proof_HF tl h_inner.
                                # Apply IH at tl with disjunct
                                # (mem_l tl f \/ mem_l p2 f).
                                p.have("ih_disj: mem_l tl f \\/ mem_l p2 f").by_disj(
                                    "mem_in_tl"
                                )
                                p.have("mem_app_tl: mem_l (append_l tl p2) f").by(
                                    "IH",
                                    "tl",
                                    "lt_tl_p1",
                                    "h_inner",
                                    "h_inner_eq",
                                    "p2",
                                    "f",
                                    "ih_disj",
                                )
                                p.have(
                                    "right_disj: f = hd_v \\/ mem_l (append_l tl p2) f"
                                ).by_disj("mem_app_tl")
                                p.have(
                                    "mem_app_cons: "
                                    "mem_l (cons_l hd_v "
                                    "(append_l tl p2)) f"
                                ).by_eq_mp(
                                    SYM(mem_cons_app),
                                    "right_disj",
                                )
                                p.thus("mem_l (append_l p1 p2) f").by_rewrite_of(
                                    "mem_app_cons",
                                    [SYM(p.fact("app_eq"))],
                                )
            with p.case("from2: mem_l p2 f"):
                # mem_l (append_l tl p2) f from mem_l p2 f.
                with p.cases_on("tail_disj"):
                    with p.case("tnil: tl = nil_l"):
                        # append_l nil_l p2 = p2.
                        ap_nil = SPEC(p._parse("p2"), APPEND_L_AT_NIL)
                        # ap_nil : append_l nil_l p2 = p2
                        p.have("app_tl_eq_p2: append_l tl p2 = p2").by_rewrite_of(
                            ap_nil, [SYM(p.fact("tnil"))]
                        )
                        # Lift app_tl_eq_p2 through mem_l to get
                        # mem_l (append_l tl p2) f = mem_l p2 f, then
                        # EQ_MP (sym-tolerant) lands on the LHS.
                        mem_app_eq_th = AP_THM(
                            AP_TERM(mem_l, p.fact("app_tl_eq_p2")),
                            p._parse("f"),
                        )
                        p.have("mem_app_tl: mem_l (append_l tl p2) f").by_eq_mp(
                            mem_app_eq_th, "from2"
                        )
                        p.have(
                            "right_disj: f = hd_v \\/ mem_l (append_l tl p2) f"
                        ).by_disj("mem_app_tl")
                        p.have(
                            "mem_app_cons: mem_l (cons_l hd_v (append_l tl p2)) f"
                        ).by_eq_mp(SYM(mem_cons_app), "right_disj")
                        p.thus("mem_l (append_l p1 p2) f").by_rewrite_of(
                            "mem_app_cons",
                            [SYM(p.fact("app_eq"))],
                        )
                    with p.case("tex: ?h_inner. Proof_HF tl h_inner"):
                        p.have("ih_disj: mem_l tl f \\/ mem_l p2 f").by_disj("from2")
                        p.have("mem_app_tl: mem_l (append_l tl p2) f").by(
                            "IH",
                            "tl",
                            "lt_tl_p1",
                            "h_inner",
                            "h_inner_eq",
                            "p2",
                            "f",
                            "ih_disj",
                        )
                        p.have(
                            "right_disj: f = hd_v \\/ mem_l (append_l tl p2) f"
                        ).by_disj("mem_app_tl")
                        p.have(
                            "mem_app_cons: mem_l (cons_l hd_v (append_l tl p2)) f"
                        ).by_eq_mp(SYM(mem_cons_app), "right_disj")
                        p.thus("mem_l (append_l p1 p2) f").by_rewrite_of(
                            "mem_app_cons",
                            [SYM(p.fact("app_eq"))],
                        )


# ---------------------------------------------------------------------------
# Stage 3B (f) -- ``valid_step`` preservation under membership extension.
#
#   |- !q1 q2 hd. (!f. mem_l q1 f ==> mem_l q2 f)
#                 ==> valid_step q1 hd ==> valid_step q2 hd.
#
# Direct case-split on the disjunction inside ``valid_step``: the
# axiom case is unaffected by the change of step list; the MP and Gen
# cases consume ``mem_l q1 _`` premises which lift to ``mem_l q2 _``
# via the supplied preservation hypothesis.
# ---------------------------------------------------------------------------


@proof
def VALID_STEP_PRESERVES(p):
    """|- !q1 q2 hd. (!f. mem_l q1 f ==> mem_l q2 f)
    ==> valid_step q1 hd ==> valid_step q2 hd."""
    p.goal(
        "!q1 q2 hd. (!f. mem_l q1 f ==> mem_l q2 f) "
        "==> valid_step q1 hd ==> valid_step q2 hd"
    )
    p.fix("q1 q2 hd")
    p.assume("preserve: !f. mem_l q1 f ==> mem_l q2 f")
    p.assume("v1: valid_step q1 hd")

    valid_at_1 = SPECL([p._parse("q1"), p._parse("hd")], VALID_STEP_AT)
    valid_at_2 = SPECL([p._parse("q2"), p._parse("hd")], VALID_STEP_AT)

    vd1_str = (
        "is_axiom hd "
        "\\/ (?f1 f2. mem_l q1 f1 /\\ mem_l q1 f2 "
        "/\\ is_mp f1 f2 hd) "
        "\\/ (?f1. mem_l q1 f1 /\\ is_gen f1 hd)"
    )
    vd2_str = (
        "is_axiom hd "
        "\\/ (?f1 f2. mem_l q2 f1 /\\ mem_l q2 f2 "
        "/\\ is_mp f1 f2 hd) "
        "\\/ (?f1. mem_l q2 f1 /\\ is_gen f1 hd)"
    )
    p.have(f"v1d: {vd1_str}").by_eq_mp(valid_at_1, "v1")

    with p.cases_on("v1d"):
        with p.case("ax_c: is_axiom hd"):
            p.have(f"v2d: {vd2_str}").by_disj("ax_c")
            p.thus("valid_step q2 hd").by_eq_mp(SYM(valid_at_2), "v2d")
        with p.case("mp_c: ?f1 f2. mem_l q1 f1 /\\ mem_l q1 f2 /\\ is_mp f1 f2 hd"):
            p.split("f2_eq", "(mem_q1_f1, mem_q1_f2, mp_th)")
            p.have("mem_q2_f1: mem_l q2 f1").by("preserve", "f1", "mem_q1_f1")
            p.have("mem_q2_f2: mem_l q2 f2").by("preserve", "f2", "mem_q1_f2")
            p.have(
                "new_mp: ?f1 f2. mem_l q2 f1 /\\ mem_l q2 f2 /\\ is_mp f1 f2 hd"
            ).by_exists(
                ["f1", "f2"],
                "mem_q2_f1",
                "mem_q2_f2",
                "mp_th",
            )
            p.have(f"v2d: {vd2_str}").by_disj("new_mp")
            p.thus("valid_step q2 hd").by_eq_mp(SYM(valid_at_2), "v2d")
        with p.case("gen_c: ?f1. mem_l q1 f1 /\\ is_gen f1 hd"):
            p.split("f1_eq", "(mem_q1_f1, gen_th)")
            p.have("mem_q2_f1: mem_l q2 f1").by("preserve", "f1", "mem_q1_f1")
            p.have("new_gen: ?f1. mem_l q2 f1 /\\ is_gen f1 hd").by_exists(
                ["f1"], "mem_q2_f1", "gen_th"
            )
            p.have(f"v2d: {vd2_str}").by_disj("new_gen")
            p.thus("valid_step q2 hd").by_eq_mp(SYM(valid_at_2), "v2d")


# ---------------------------------------------------------------------------
# Stage 3B (g) -- ``Proof_HF`` is preserved under list concatenation.
#
#   |- !p1 h1. Proof_HF p1 h1 ==>
#       !p2 h2. Proof_HF p2 h2 ==> Proof_HF (append_l p1 p2) h1.
#
# Strong induction on ``p1``. Unpack ``Proof_HF p1 h1`` to
# ``p1 = cons_l hd tl`` and case-split on the inner tail disjunct:
#
#   * ``tl = nil_l``: ``append_l p1 p2 = cons_l hd p2``. The membership
#     premise is vacuous (``mem_l nil_l _ = F``) so ``valid_step nil_l hd
#     ==> valid_step p2 hd`` discharges trivially via
#     ``VALID_STEP_PRESERVES``. Tail-of-tail disjunct uses ``Proof_HF p2 h2``.
#
#   * ``Proof_HF tl h_inner``: IH at ``tl`` gives
#     ``Proof_HF (append_l tl p2) h_inner``; ``MEM_L_APPEND_PRESERVES`` (with
#     ``mem_l tl f \\/ mem_l p2 f`` ⇒ ``mem_l (append_l tl p2) f``) lifts
#     ``valid_step tl hd`` into ``valid_step (append_l tl p2) hd``.
# ---------------------------------------------------------------------------


@proof
def PROOF_HF_APPEND(p):
    """|- !p1 h1 p2 h2. Proof_HF p1 h1 ==> Proof_HF p2 h2
    ==> Proof_HF (append_l p1 p2) h1."""
    p.goal(
        "!p1. !h1. Proof_HF p1 h1 ==> "
        "!p2 h2. Proof_HF p2 h2 "
        "==> Proof_HF (append_l p1 p2) h1"
    )
    with p.strong_induction("p1", "IH"):
        p.fix("h1")
        p.assume("pq1: Proof_HF p1 h1")
        p.fix("p2 h2")
        p.assume("pq2: Proof_HF p2 h2")

        rec_pq1 = SPECL([p._parse("p1"), p._parse("h1")], PROOF_HF_REC_PW)
        body_str = (
            "?h t. p1 = cons_l h t /\\ h = h1 /\\ valid_step t h "
            "/\\ (t = nil_l \\/ ?h_inner. Proof_HF t h_inner)"
        )
        p.have(f"body: {body_str}").by_eq_mp(rec_pq1, "pq1")
        p.choose("hd", "body", eq_label="ex_t")
        p.choose("tl", "ex_t", eq_label="conj")
        p.split("conj", "(p_eq_cons, hd_eq_h1, valid_th, tail_disj)")

        lt_t_cons = SPECL([p._parse("hd"), p._parse("tl")], NAT0_LT_CONS_L_TAIL)
        p.have("lt_tl_p1: nat0_lt tl p1").by_rewrite_of(
            lt_t_cons, [SYM(p.fact("p_eq_cons"))]
        )

        ap_at = SPECL(
            [p._parse("hd"), p._parse("tl"), p._parse("p2")],
            APPEND_L_AT_CONS,
        )
        p.have("app_eq: append_l p1 p2 = cons_l hd (append_l tl p2)").by_rewrite_of(
            ap_at, [SYM(p.fact("p_eq_cons"))]
        )

        target_eq = SPECL(
            [p._parse("hd"), p._parse("append_l tl p2"), p._parse("h1")],
            PROOF_HF_AT_CONS,
        )

        with p.cases_on("tail_disj"):
            with p.case("tnil: tl = nil_l"):
                ap_nil = SPEC(p._parse("p2"), APPEND_L_AT_NIL)
                p.have("app_tl_eq_p2: append_l tl p2 = p2").by_rewrite_of(
                    ap_nil, [SYM(p.fact("tnil"))]
                )

                with p.have("preserve: !f. mem_l tl f ==> mem_l p2 f").proof():
                    p.fix("f")
                    p.assume("mem_tl: mem_l tl f")
                    p.have("mem_nil: mem_l nil_l f").by_rewrite_of(
                        "mem_tl", [p.fact("tnil")]
                    )
                    mem_nil_at = SPEC(p._parse("f"), MEM_L_AT_NIL)
                    p.have("F_th: F").by_eq_mp(mem_nil_at, "mem_nil")
                    p.thus("mem_l p2 f").by_thm(
                        CONTR(
                            p._parse("mem_l p2 f"),
                            p.fact("F_th"),
                        )
                    )

                p.have("valid_p2: valid_step p2 hd").by(
                    VALID_STEP_PRESERVES, "tl", "p2", "hd", "preserve", "valid_th"
                )
                # Lift via SYM(app_tl_eq_p2). Since RHS p2 not LHS
                # append_l tl p2, use AP_TERM/AP_THM bridge + by_eq_mp.
                vs_eq = AP_THM(
                    AP_TERM(valid_step, p.fact("app_tl_eq_p2")),
                    p._parse("hd"),
                )
                # vs_eq : valid_step (append_l tl p2) hd = valid_step p2 hd.
                p.have("valid_app: valid_step (append_l tl p2) hd").by_eq_mp(
                    vs_eq, "valid_p2"
                )

                # Proof_HF p2 h2 lifts to Proof_HF (append_l tl p2) h2.
                pq_eq = AP_THM(
                    AP_TERM(Proof_HF, p.fact("app_tl_eq_p2")),
                    p._parse("h2"),
                )
                p.have("pq_app: Proof_HF (append_l tl p2) h2").by_eq_mp(pq_eq, "pq2")
                p.have("ex_app: ?h_inner. Proof_HF (append_l tl p2) h_inner").by_witness(
                    "h2", "pq_app"
                )
                p.have(
                    "tail_app_disj: "
                    "(append_l tl p2) = nil_l "
                    "\\/ ?h_inner. Proof_HF (append_l tl p2) h_inner"
                ).by_disj("ex_app")

                p.have(
                    "target_body: hd = h1 /\\ "
                    "valid_step (append_l tl p2) hd /\\ "
                    "((append_l tl p2) = nil_l "
                    "\\/ ?h_inner. Proof_HF (append_l tl p2) h_inner)"
                ).by_thm(
                    CONJ(
                        p.fact("hd_eq_h1"),
                        CONJ(p.fact("valid_app"), p.fact("tail_app_disj")),
                    )
                )
                p.have("pq_cons: Proof_HF (cons_l hd (append_l tl p2)) h1").by_eq_mp(
                    SYM(target_eq), "target_body"
                )
                p.thus("Proof_HF (append_l p1 p2) h1").by_rewrite_of(
                    "pq_cons", [SYM(p.fact("app_eq"))]
                )

            with p.case("tex: ?h_inner. Proof_HF tl h_inner"):
                with p.have(
                    "preserve: !f. mem_l tl f ==> mem_l (append_l tl p2) f"
                ).proof():
                    p.fix("f")
                    p.assume("mem_tl: mem_l tl f")
                    p.have("ih_disj: mem_l tl f \\/ mem_l p2 f").by_disj("mem_tl")
                    p.thus("mem_l (append_l tl p2) f").by(
                        MEM_L_APPEND_PRESERVES,
                        "tl",
                        "h_inner",
                        "h_inner_eq",
                        "p2",
                        "f",
                        "ih_disj",
                    )

                p.have("valid_app: valid_step (append_l tl p2) hd").by(
                    VALID_STEP_PRESERVES,
                    "tl",
                    "append_l tl p2",
                    "hd",
                    "preserve",
                    "valid_th",
                )

                p.have("pq_app: Proof_HF (append_l tl p2) h_inner").by(
                    "IH", "tl", "lt_tl_p1", "h_inner", "h_inner_eq", "p2", "h2", "pq2"
                )

                p.have("ex_app: ?h_inner. Proof_HF (append_l tl p2) h_inner").by_witness(
                    "h_inner", "pq_app"
                )
                p.have(
                    "tail_app_disj: "
                    "(append_l tl p2) = nil_l "
                    "\\/ ?h_inner. Proof_HF (append_l tl p2) h_inner"
                ).by_disj("ex_app")

                p.have(
                    "target_body: hd = h1 /\\ "
                    "valid_step (append_l tl p2) hd /\\ "
                    "((append_l tl p2) = nil_l "
                    "\\/ ?h_inner. Proof_HF (append_l tl p2) h_inner)"
                ).by_thm(
                    CONJ(
                        p.fact("hd_eq_h1"),
                        CONJ(p.fact("valid_app"), p.fact("tail_app_disj")),
                    )
                )
                p.have("pq_cons: Proof_HF (cons_l hd (append_l tl p2)) h1").by_eq_mp(
                    SYM(target_eq), "target_body"
                )
                p.thus("Proof_HF (append_l p1 p2) h1").by_rewrite_of(
                    "pq_cons", [SYM(p.fact("app_eq"))]
                )


# ---------------------------------------------------------------------------
# Stage 3B (h) -- ``Proof_HF p h ==> mem_l p h`` (head is its own member).
# ---------------------------------------------------------------------------


@proof
def PROOF_HF_HEAD_MEM(p):
    """|- !p1 h1. Proof_HF p1 h1 ==> mem_l p1 h1."""
    p.goal("!p1 h1. Proof_HF p1 h1 ==> mem_l p1 h1")
    p.fix("p1 h1")
    p.assume("pq: Proof_HF p1 h1")
    rec_pq = SPECL([p._parse("p1"), p._parse("h1")], PROOF_HF_REC_PW)
    body_str = (
        "?h t. p1 = cons_l h t /\\ h = h1 /\\ valid_step t h "
        "/\\ (t = nil_l \\/ ?h_inner. Proof_HF t h_inner)"
    )
    p.have(f"body: {body_str}").by_eq_mp(rec_pq, "pq")
    p.choose("hd", "body", eq_label="ex_t")
    p.choose("tl", "ex_t", eq_label="conj")
    p.split("conj", "(p_eq_cons, hd_eq_h1, _v, _td)")

    mem_at_cons = SPECL(
        [p._parse("hd"), p._parse("tl"), p._parse("hd")],
        MEM_L_AT_CONS,
    )
    p.have("hd_disj: hd = hd \\/ mem_l tl hd").by_disj(REFL(p._parse("hd")))
    p.have("mem_at: mem_l (cons_l hd tl) hd").by_eq_mp(SYM(mem_at_cons), "hd_disj")
    p.have("mem_p_hd: mem_l p1 hd").by_rewrite_of("mem_at", [SYM(p.fact("p_eq_cons"))])
    p.thus("mem_l p1 h1").by_rewrite_of("mem_p_hd", [p.fact("hd_eq_h1")])


# ---------------------------------------------------------------------------
# Stage 3B (i) -- legacy list-proof admissibility clauses.
#
# These no longer define the active ``Prov_HF`` route; the set-native
# closure rules below use ``Proof_HF_set`` instead.
# ---------------------------------------------------------------------------


@proof
def AXIOM_HAS_PROOF(p):
    """|- !m. is_axiom m ==> ?p. Proof_HF p m.

    Witness: ``cons_l m nil_l``. Validity: ``valid_step nil_l m``
    follows directly from ``is_axiom m`` via the axiom disjunct;
    tail disjunct collapses to ``nil_l = nil_l``.
    """
    p.goal("!m. is_axiom m ==> ?p. Proof_HF p m")
    p.fix("m")
    p.assume("ax: is_axiom m")

    valid_at = SPECL([nil_l, p._parse("m")], VALID_STEP_AT)
    vd_str = (
        "is_axiom m \\/ "
        "(?f1 f2. mem_l nil_l f1 /\\ mem_l nil_l f2 "
        "/\\ is_mp f1 f2 m) \\/ "
        "(?f1. mem_l nil_l f1 /\\ is_gen f1 m)"
    )
    p.have(f"vd: {vd_str}").by_disj("ax")
    p.have("valid_th: valid_step nil_l m").by_eq_mp(SYM(valid_at), "vd")
    p.have("tail_disj: nil_l = nil_l \\/ ?h_inner. Proof_HF nil_l h_inner").by_disj(
        REFL(nil_l)
    )

    target_eq = SPECL(
        [p._parse("m"), nil_l, p._parse("m")],
        PROOF_HF_AT_CONS,
    )
    p.have(
        "target_body: m = m /\\ valid_step nil_l m "
        "/\\ (nil_l = nil_l "
        "\\/ ?h_inner. Proof_HF nil_l h_inner)"
    ).by_thm(
        CONJ(
            REFL(p._parse("m")),
            CONJ(p.fact("valid_th"), p.fact("tail_disj")),
        )
    )
    p.have("pq_witness: Proof_HF (cons_l m nil_l) m").by_eq_mp(
        SYM(target_eq), "target_body"
    )
    p.thus("?p. Proof_HF p m").by_witness("cons_l m nil_l", "pq_witness")


@proof
def GEN_HAS_PROOF(p):
    """|- !f x. (?p1. Proof_HF p1 f) ==>
                ?p. Proof_HF p (Forall_f x f).

    Witness: ``cons_l (Forall_f x f) p1``. Validity: Gen disjunct of
    ``valid_step p1 (Forall_f x f)`` with member ``f`` (head of ``p1``)
    and ``is_gen f (Forall_f x f)`` (witness ``x`` for the inner
    existential). Tail disjunct: right with witness ``f`` (since
    ``Proof_HF p1 f``).
    """
    p.goal("!f x. (?p1. Proof_HF p1 f) ==> ?p. Proof_HF p (Forall_f x f)")
    p.fix("f x")
    p.assume("pq_ex: ?p1. Proof_HF p1 f")
    p.choose("p1", "pq_ex", eq_label="pq1")

    p.have("mem_p1_f: mem_l p1 f").by(PROOF_HF_HEAD_MEM, "p1", "f", "pq1")

    # is_gen f (Forall_f x f): ?y. Forall_f x f = Forall_f y f, witness y := x.
    is_gen_at = SPECL([p._parse("f"), p._parse("Forall_f x f")], IS_GEN_AT)
    # is_gen_at : is_gen f (Forall_f x f) = (?y. Forall_f x f = Forall_f y f).
    p.have("exists_y: ?y. Forall_f x f = Forall_f y f").by_witness(
        "x", REFL(p._parse("Forall_f x f"))
    )
    p.have("gen_th: is_gen f (Forall_f x f)").by_eq_mp(SYM(is_gen_at), "exists_y")

    # valid_step p1 (Forall_f x f) via Gen disjunct.
    valid_at = SPECL([p._parse("p1"), p._parse("Forall_f x f")], VALID_STEP_AT)
    p.have("gen_ex: ?f1. mem_l p1 f1 /\\ is_gen f1 (Forall_f x f)").by_exists(
        ["f"], "mem_p1_f", "gen_th"
    )
    vd_str = (
        "is_axiom (Forall_f x f) \\/ "
        "(?f1 f2. mem_l p1 f1 /\\ mem_l p1 f2 "
        "/\\ is_mp f1 f2 (Forall_f x f)) \\/ "
        "(?f1. mem_l p1 f1 /\\ is_gen f1 (Forall_f x f))"
    )
    p.have(f"vd: {vd_str}").by_disj("gen_ex")
    p.have("valid_th: valid_step p1 (Forall_f x f)").by_eq_mp(SYM(valid_at), "vd")

    # Tail disjunct: ?h_inner. Proof_HF p1 h_inner with witness f.
    p.have("tail_ex: ?h_inner. Proof_HF p1 h_inner").by_witness("f", "pq1")
    p.have("tail_disj: p1 = nil_l \\/ ?h_inner. Proof_HF p1 h_inner").by_disj("tail_ex")

    fa_t = p._parse("Forall_f x f")
    target_eq = SPECL(
        [fa_t, p._parse("p1"), fa_t],
        PROOF_HF_AT_CONS,
    )
    p.have(
        "target_body: Forall_f x f = Forall_f x f "
        "/\\ valid_step p1 (Forall_f x f) "
        "/\\ (p1 = nil_l "
        "\\/ ?h_inner. Proof_HF p1 h_inner)"
    ).by_thm(
        CONJ(
            REFL(fa_t),
            CONJ(p.fact("valid_th"), p.fact("tail_disj")),
        )
    )
    p.have("pq_witness: Proof_HF (cons_l (Forall_f x f) p1) (Forall_f x f)").by_eq_mp(
        SYM(target_eq), "target_body"
    )
    p.thus("?p. Proof_HF p (Forall_f x f)").by_witness(
        "cons_l (Forall_f x f) p1", "pq_witness"
    )


@proof
def MP_HAS_PROOF(p):
    """|- !f g. (?p1. Proof_HF p1 f) /\\ (?p2. Proof_HF p2 (Imp_f f g))
                 ==> ?p. Proof_HF p g.

    Witness: ``cons_l g (append_l p2 p1)``. Validity: MP disjunct
    with ``f1 := f``, ``f2 := Imp_f f g`` -- both members of
    ``append_l p2 p1`` via ``MEM_L_APPEND_PRESERVES`` (lifting
    ``mem_l p2 (Imp_f f g)`` and ``mem_l p1 f``). Tail disjunct:
    ``Proof_HF (append_l p2 p1) (Imp_f f g)`` from ``PROOF_HF_APPEND``.
    """
    p.goal(
        "!f g. (?p1. Proof_HF p1 f) /\\ "
        "(?p2. Proof_HF p2 (Imp_f f g)) "
        "==> ?p. Proof_HF p g"
    )
    p.fix("f g")
    p.assume("(pq1_ex, pq2_ex): (?p1. Proof_HF p1 f) /\\ (?p2. Proof_HF p2 (Imp_f f g))")
    p.choose("p1", "pq1_ex", eq_label="pq1")
    p.choose("p2", "pq2_ex", eq_label="pq2")

    # Members.
    p.have("mem_p1_f: mem_l p1 f").by(PROOF_HF_HEAD_MEM, "p1", "f", "pq1")
    p.have("mem_p2_imp: mem_l p2 (Imp_f f g)").by(
        PROOF_HF_HEAD_MEM, "p2", "Imp_f f g", "pq2"
    )

    # Lift via MEM_L_APPEND_PRESERVES with (p1' := p2, p2' := p1):
    #   Proof_HF p2 (Imp_f f g) ==> (mem_l p2 a \/ mem_l p1 a) ==>
    #     mem_l (append_l p2 p1) a.
    p.have("disj_imp: mem_l p2 (Imp_f f g) \\/ mem_l p1 (Imp_f f g)").by_disj(
        "mem_p2_imp"
    )
    p.have("mem_app_imp: mem_l (append_l p2 p1) (Imp_f f g)").by(
        MEM_L_APPEND_PRESERVES, "p2", "Imp_f f g", "pq2", "p1", "Imp_f f g", "disj_imp"
    )
    p.have("disj_f: mem_l p2 f \\/ mem_l p1 f").by_disj("mem_p1_f")
    p.have("mem_app_f: mem_l (append_l p2 p1) f").by(
        MEM_L_APPEND_PRESERVES, "p2", "Imp_f f g", "pq2", "p1", "f", "disj_f"
    )

    # is_mp f (Imp_f f g) g  =  (Imp_f f g = Imp_f f g).
    is_mp_at = SPECL(
        [p._parse("f"), p._parse("Imp_f f g"), p._parse("g")],
        IS_MP_AT,
    )
    p.have("is_mp_th: is_mp f (Imp_f f g) g").by_eq_mp(
        SYM(is_mp_at), REFL(p._parse("Imp_f f g"))
    )

    p.have(
        "mp_ex: ?f1 f2. mem_l (append_l p2 p1) f1 "
        "/\\ mem_l (append_l p2 p1) f2 "
        "/\\ is_mp f1 f2 g"
    ).by_exists(
        ["f", "Imp_f f g"],
        "mem_app_f",
        "mem_app_imp",
        "is_mp_th",
    )
    app_t = p._parse("append_l p2 p1")
    g_t = p._parse("g")
    valid_at = SPECL([app_t, g_t], VALID_STEP_AT)
    vd_str = (
        "is_axiom g \\/ "
        "(?f1 f2. mem_l (append_l p2 p1) f1 "
        "/\\ mem_l (append_l p2 p1) f2 "
        "/\\ is_mp f1 f2 g) \\/ "
        "(?f1. mem_l (append_l p2 p1) f1 /\\ is_gen f1 g)"
    )
    p.have(f"vd: {vd_str}").by_disj("mp_ex")
    p.have("valid_th: valid_step (append_l p2 p1) g").by_eq_mp(SYM(valid_at), "vd")

    # Tail disjunction: ?h_inner. Proof_HF (append_l p2 p1) h_inner via
    # PROOF_HF_APPEND with witness Imp_f f g.
    p.have("pq_app: Proof_HF (append_l p2 p1) (Imp_f f g)").by(
        PROOF_HF_APPEND, "p2", "Imp_f f g", "pq2", "p1", "f", "pq1"
    )
    p.have("tail_ex: ?h_inner. Proof_HF (append_l p2 p1) h_inner").by_witness(
        "Imp_f f g", "pq_app"
    )
    p.have(
        "tail_disj: (append_l p2 p1) = nil_l "
        "\\/ ?h_inner. Proof_HF (append_l p2 p1) h_inner"
    ).by_disj("tail_ex")

    target_eq = SPECL([g_t, app_t, g_t], PROOF_HF_AT_CONS)
    p.have(
        "target_body: g = g "
        "/\\ valid_step (append_l p2 p1) g "
        "/\\ ((append_l p2 p1) = nil_l "
        "\\/ ?h_inner. Proof_HF (append_l p2 p1) h_inner)"
    ).by_thm(
        CONJ(
            REFL(g_t),
            CONJ(p.fact("valid_th"), p.fact("tail_disj")),
        )
    )
    p.have("pq_witness: Proof_HF (cons_l g (append_l p2 p1)) g").by_eq_mp(
        SYM(target_eq), "target_body"
    )
    p.thus("?p. Proof_HF p g").by_witness("cons_l g (append_l p2 p1)", "pq_witness")


# ---------------------------------------------------------------------------
# Stage 3B (j) -- set-native Sigma_1 definition of Prov_HF.
#
#   Prov_HF n  :<=>  ?P. Proof_HF_set P n.
#
# This is the canonical HF-native form: provability is the existence of
# a ranked finite HF-set proof object. The legacy list checker remains
# external scaffolding only; it is not used by ``Prov_HF``.
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
# Headline theorem (``SUBSTITUTE_REPRESENTS``, body in hf_repr_thms.py):
#   |- !F t v. Prov_HF (
#         substitute (substitute (substitute (substitute
#             substitute_internal (numeral F) var_x)
#             (numeral t) var_y)
#             (numeral v) var_z)
#             (numeral (substitute F t v)) var_w).
#
# ``substitute_internal`` is a HF-formula in four free variables --
# ``var_x`` (F-slot), ``var_y`` (t-slot), ``var_z`` (v-slot), ``var_w``
# (result-slot) -- expressing the relation "substitute(F, t, v) = r".
#
# Why a single fixed Sigma_1 formula (not a HOL-recursive family): the
# diagonal lemma (Stage 3D) forms the Goedel sentence by substituting a
# numeric godelnum into a *single fixed* internal-provability formula.
# Without ``substitute_internal`` as one fixed HF-formula, no ``D(x, y)``
# represents the diagonal function and the fixed-point construction
# collapses.
#
# Encoding strategy: ``substitute_internal`` is the Sigma_1 predicate
#     ?T. is_substitute_trace T F t v r
# where T : nat0 is an HF set of (subterm-shape, output-shape) pairs
# (Pair_ord-encoded), and is_substitute_trace asserts:
#   (i)  the input pair (F, r) is in T;
#   (ii) every (a, b) in T satisfies the structural-recursion clause
#        matching substitute's SUBSTITUTE_AT_* equations -- a bounded
#        conjunction over its members via In, decoded by Pair_ord
#        projection.
# HF proves substitute_internal at every numeral instance by exhibiting
# the trace HF set explicitly; verification conjuncts are decidable
# equalities + In-membership facts, all Sigma_0 in HF.
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


# var_T -- HF-internal bound variable for the existentially-quantified HF
# trace set inside ``substitute_internal``. Index 4 (SUC0^4 0); the four
# free slots var_x/y/z/w (indices 0..3) are reserved for the input/output
# pair (F, t, v, r).
VAR_T_DEF = define(
    "var_T",
    parse_type("nat0"),
    "Var_t (SUC0 (SUC0 (SUC0 (SUC0 0))))",
)
var_T = mk_const("var_T", [])

IDX_T_DEF = define("idx_T", parse_type("nat0"), "SUC0 (SUC0 (SUC0 (SUC0 0)))")
idx_T = mk_const("idx_T", [])


# Additional HF-internal variables for the body of is_substitute_trace_internal:
#   var_a, var_b           -- the "!a b. ..." outer for-all binders.
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
# is_substitute_step T t v a b -- "(a, b) is a valid substitute clause".
#
# Sigma_0 (decidable) HOL predicate. Holds iff the pair (a, b) matches one
# of the 9 SUBSTITUTE_AT_* clauses with respect to the substitution
# parameters (t, v) and a trace HF set T:
#   * Constant-shape clauses (Empty_t, Var_t at v, Var_t off v, Forall_f
#     hit) require no trace consultations -- b is determined by a alone.
#   * Recursive clauses (Not_f, the binary constructors Eq_f / Imp_f /
#     Insert_t / In_a, and Forall_f miss) require the corresponding
#     sub-shape pairs to be in T, witnessed via In (Pair_ord _ _) T.
#
# This predicate is the HOL counterpart of the HF-formula
# ``is_substitute_trace_internal`` to be encoded in Stage B1; the trace
# existence lemma in Stage A4 builds an HF set T satisfying
# ``In_a (Pair_ord F r) T /\ !a b. In (Pair_ord a b) T ==>
#  is_substitute_step T t v a b``.
# ---------------------------------------------------------------------------

_a_step = Var("a", nat0_ty)
_b_step = Var("b", nat0_ty)
_t_step = Var("t", nat0_ty)
_v_step = Var("v", nat0_ty)
_T_step = Var("T", nat0_ty)


# Pointwise: |- !T t v a b. is_substitute_step T t v a b = body[T,t,v,a,b].
IS_SUBSTITUTE_STEP_DEF, IS_SUBSTITUTE_STEP_AT = define_with_at(
    "is_substitute_step",
    parse_type("nat0 -> nat0 -> nat0 -> nat0 -> nat0 -> bool"),
    "\\T:nat0. \\t:nat0. \\v:nat0. \\a:nat0. \\b:nat0. "
    "(a = Empty_t /\\ b = Empty_t) "
    "\\/ (a = Var_t v /\\ b = t) "
    "\\/ (?w. a = Var_t w /\\ ~(w = v) /\\ b = Var_t w) "
    "\\/ (?a1 a2 b1 b2. a = Eq_f a1 a2 /\\ b = Eq_f b1 b2 "
    "      /\\ In (Pair_ord a1 b1) T /\\ In (Pair_ord a2 b2) T) "
    "\\/ (?s1 s2. a = Not_f s1 /\\ b = Not_f s2 /\\ In (Pair_ord s1 s2) T) "
    "\\/ (?a1 a2 b1 b2. a = Imp_f a1 a2 /\\ b = Imp_f b1 b2 "
    "      /\\ In (Pair_ord a1 b1) T /\\ In (Pair_ord a2 b2) T) "
    "\\/ (?w f1. a = Forall_f w f1 /\\ w = v /\\ b = Forall_f w f1) "
    "\\/ (?w f1 f2. a = Forall_f w f1 /\\ ~(w = v) "
    "      /\\ b = Forall_f w f2 /\\ In (Pair_ord f1 f2) T) "
    "\\/ (?a1 a2 b1 b2. a = Insert_t a1 a2 /\\ b = Insert_t b1 b2 "
    "      /\\ In (Pair_ord a1 b1) T /\\ In (Pair_ord a2 b2) T) "
    "\\/ (?a1 a2 b1 b2. a = In_a a1 a2 /\\ b = In_a b1 b2 "
    "      /\\ In (Pair_ord a1 b1) T /\\ In (Pair_ord a2 b2) T)",
)
is_substitute_step = mk_const("is_substitute_step", [])


# ---------------------------------------------------------------------------
# is_substitute_trace T F t v r -- "T is a complete substitute trace
# witnessing  r = substitute F t v".
#
#   is_substitute_trace T F t v r :=
#       In (Pair_ord F r) T
#       /\ (!a b. In (Pair_ord a b) T ==> is_substitute_step T t v a b).
#
# Two conjuncts:
#   (i)  the headline (F, r) pair is in T, so r is the recorded substitute
#        result for F;
#   (ii) every member of T is a valid substitute clause (witnessed by the
#        Sigma_0 recogniser ``is_substitute_step``), so the trace as a
#        whole is internally consistent and grounded in the SUBSTITUTE_AT_*
#        equations.
#
# ``IS_SUBSTITUTE_TRACE_AT`` exposes this body pointwise for downstream
# rewriting; the @ args go in the canonical order T, F, t, v, r.
# ---------------------------------------------------------------------------

_T_n0 = Var("T", nat0_ty)
_F_n0 = Var("F", nat0_ty)
_tt_n0 = Var("t", nat0_ty)
_vv_n0 = Var("v", nat0_ty)
_rr_n0 = Var("r", nat0_ty)


# Pointwise: |- !T F t v r. is_substitute_trace T F t v r =
#                          In (Pair_ord F r) T /\
#                          (!a b. In (Pair_ord a b) T ==>
#                                 is_substitute_step T t v a b).
IS_SUBSTITUTE_TRACE_DEF, IS_SUBSTITUTE_TRACE_AT = define_with_at(
    "is_substitute_trace",
    parse_type("nat0 -> nat0 -> nat0 -> nat0 -> nat0 -> bool"),
    "\\T:nat0. \\F:nat0. \\t:nat0. \\v:nat0. \\r:nat0. "
    "In (Pair_ord F r) T "
    "/\\ (!a b. In (Pair_ord a b) T ==> is_substitute_step T t v a b)",
)
is_substitute_trace = mk_const("is_substitute_trace", [])


# String-templated 9-disjunction body of is_substitute_step, with the
# trace HF set ``T`` substituted in. Used by TRACE_STEP_MONO so the same
# disjunction can be referenced under both T1 and T2 without copy-paste.
def _is_step_body(T):
    return (
        f"(a = Empty_t /\\ b = Empty_t) "
        f"\\/ (a = Var_t v /\\ b = t) "
        f"\\/ (?w. a = Var_t w /\\ ~(w = v) /\\ b = Var_t w) "
        f"\\/ (?a1 a2 b1 b2. a = Eq_f a1 a2 /\\ b = Eq_f b1 b2 "
        f"      /\\ In (Pair_ord a1 b1) {T} /\\ In (Pair_ord a2 b2) {T}) "
        f"\\/ (?s1 s2. a = Not_f s1 /\\ b = Not_f s2 "
        f"      /\\ In (Pair_ord s1 s2) {T}) "
        f"\\/ (?a1 a2 b1 b2. a = Imp_f a1 a2 /\\ b = Imp_f b1 b2 "
        f"      /\\ In (Pair_ord a1 b1) {T} /\\ In (Pair_ord a2 b2) {T}) "
        f"\\/ (?w f1. a = Forall_f w f1 /\\ w = v /\\ b = Forall_f w f1) "
        f"\\/ (?w f1 f2. a = Forall_f w f1 /\\ ~(w = v) "
        f"      /\\ b = Forall_f w f2 /\\ In (Pair_ord f1 f2) {T}) "
        f"\\/ (?a1 a2 b1 b2. a = Insert_t a1 a2 /\\ b = Insert_t b1 b2 "
        f"      /\\ In (Pair_ord a1 b1) {T} /\\ In (Pair_ord a2 b2) {T}) "
        f"\\/ (?a1 a2 b1 b2. a = In_a a1 a2 /\\ b = In_a b1 b2 "
        f"      /\\ In (Pair_ord a1 b1) {T} /\\ In (Pair_ord a2 b2) {T})"
    )


@proof
def TRACE_STEP_MONO(p):
    """|- !T1 T2. (!x. In x T1 ==> In x T2) ==>
            !t v a b. is_substitute_step T1 t v a b
                      ==> is_substitute_step T2 t v a b.

    Membership-monotonicity of ``is_substitute_step``. Used by the
    binary trace-assembly cases of TRACE_EXISTS: combining sub-traces
    ``T1, T2`` into ``Insert (F, r) (Union T1 T2)`` requires lifting
    each ``In (Pair_ord _ _) T_i`` justification to the combined trace.
    """
    p.goal(
        "!T1 T2. (!x. In x T1 ==> In x T2) ==> "
        "!t v a b. is_substitute_step T1 t v a b "
        "          ==> is_substitute_step T2 t v a b"
    )
    p.fix("T1 T2")
    p.assume("hsub: !x. In x T1 ==> In x T2")
    p.fix("t v a b")
    p.assume("hstep: is_substitute_step T1 t v a b")

    body_T1 = _is_step_body("T1")
    body_T2 = _is_step_body("T2")

    p.have(f"hd1: {body_T1}").by_rewrite_of("hstep", [IS_SUBSTITUTE_STEP_AT])

    with p.have(f"hd2: {body_T2}").proof():
        with p.cases_on("hd1"):
            # 1. Empty_t (atomic).
            with p.case("c1: a = Empty_t /\\ b = Empty_t"):
                p.thus(body_T2).by_disj("c1")
            # 3. Var_t hit (atomic).
            with p.case("c3: a = Var_t v /\\ b = t"):
                p.thus(body_T2).by_disj("c3")
            # 4. Var_t miss (existential, no In).
            with p.case(
                "c4: ?w. a = Var_t w /\\ ~(w = v) /\\ b = Var_t w"
            ):
                p.thus(body_T2).by_disj("c4")
            # 7. Eq_f (binary recursive).
            with p.case(
                "c7: ?a1 a2 b1 b2. a = Eq_f a1 a2 /\\ b = Eq_f b1 b2 "
                "/\\ In (Pair_ord a1 b1) T1 /\\ In (Pair_ord a2 b2) T1"
            ):
                p.split("b2_eq", "(c7a, c7b, c7_in1, c7_in2)")
                p.have("c7_in1_T2: In (Pair_ord a1 b1) T2").by(
                    "hsub", "Pair_ord a1 b1", "c7_in1"
                )
                p.have("c7_in2_T2: In (Pair_ord a2 b2) T2").by(
                    "hsub", "Pair_ord a2 b2", "c7_in2"
                )
                p.have(
                    "c7d: ?a1 a2 b1 b2. a = Eq_f a1 a2 /\\ b = Eq_f b1 b2 "
                    "/\\ In (Pair_ord a1 b1) T2 /\\ In (Pair_ord a2 b2) T2"
                ).by_exists(
                    ["a1", "a2", "b1", "b2"],
                    "c7a", "c7b", "c7_in1_T2", "c7_in2_T2",
                )
                p.thus(body_T2).by_disj("c7d")
            # 8. Not_f (unary recursive).
            with p.case(
                "c8: ?s1 s2. a = Not_f s1 /\\ b = Not_f s2 "
                "/\\ In (Pair_ord s1 s2) T1"
            ):
                p.split("s2_eq", "(c8a, c8b, c8_in1)")
                p.have("c8_in2: In (Pair_ord s1 s2) T2").by(
                    "hsub", "Pair_ord s1 s2", "c8_in1"
                )
                p.have(
                    "c8d: ?s1 s2. a = Not_f s1 /\\ b = Not_f s2 "
                    "/\\ In (Pair_ord s1 s2) T2"
                ).by_exists(["s1", "s2"], "c8a", "c8b", "c8_in2")
                p.thus(body_T2).by_disj("c8d")
            # 9. Imp_f (binary recursive).
            with p.case(
                "c9: ?a1 a2 b1 b2. a = Imp_f a1 a2 /\\ b = Imp_f b1 b2 "
                "/\\ In (Pair_ord a1 b1) T1 /\\ In (Pair_ord a2 b2) T1"
            ):
                p.split("b2_eq", "(c9a, c9b, c9_in1, c9_in2)")
                p.have("c9_in1_T2: In (Pair_ord a1 b1) T2").by(
                    "hsub", "Pair_ord a1 b1", "c9_in1"
                )
                p.have("c9_in2_T2: In (Pair_ord a2 b2) T2").by(
                    "hsub", "Pair_ord a2 b2", "c9_in2"
                )
                p.have(
                    "c9d: ?a1 a2 b1 b2. a = Imp_f a1 a2 /\\ b = Imp_f b1 b2 "
                    "/\\ In (Pair_ord a1 b1) T2 /\\ In (Pair_ord a2 b2) T2"
                ).by_exists(
                    ["a1", "a2", "b1", "b2"],
                    "c9a", "c9b", "c9_in1_T2", "c9_in2_T2",
                )
                p.thus(body_T2).by_disj("c9d")
            # 10. Forall_f hit (existential, no In).
            with p.case(
                "c10: ?w f1. a = Forall_f w f1 /\\ w = v /\\ b = Forall_f w f1"
            ):
                p.thus(body_T2).by_disj("c10")
            # 11. Forall_f miss (existential with In).
            with p.case(
                "c11: ?w f1 f2. a = Forall_f w f1 /\\ ~(w = v) "
                "/\\ b = Forall_f w f2 /\\ In (Pair_ord f1 f2) T1"
            ):
                p.split("f2_eq", "(c11a, c11b, c11c, c11_in1)")
                p.have("c11_in2: In (Pair_ord f1 f2) T2").by(
                    "hsub", "Pair_ord f1 f2", "c11_in1"
                )
                p.have(
                    "c11d: ?w f1 f2. a = Forall_f w f1 /\\ ~(w = v) "
                    "/\\ b = Forall_f w f2 /\\ In (Pair_ord f1 f2) T2"
                ).by_exists(
                    ["w", "f1", "f2"], "c11a", "c11b", "c11c", "c11_in2"
                )
                p.thus(body_T2).by_disj("c11d")
            # 12. Insert_t (binary recursive).
            with p.case(
                "c12: ?a1 a2 b1 b2. a = Insert_t a1 a2 /\\ b = Insert_t b1 b2 "
                "/\\ In (Pair_ord a1 b1) T1 /\\ In (Pair_ord a2 b2) T1"
            ):
                p.split("b2_eq", "(c12a, c12b, c12_in1, c12_in2)")
                p.have("c12_in1_T2: In (Pair_ord a1 b1) T2").by(
                    "hsub", "Pair_ord a1 b1", "c12_in1"
                )
                p.have("c12_in2_T2: In (Pair_ord a2 b2) T2").by(
                    "hsub", "Pair_ord a2 b2", "c12_in2"
                )
                p.have(
                    "c12d: ?a1 a2 b1 b2. a = Insert_t a1 a2 "
                    "/\\ b = Insert_t b1 b2 "
                    "/\\ In (Pair_ord a1 b1) T2 /\\ In (Pair_ord a2 b2) T2"
                ).by_exists(
                    ["a1", "a2", "b1", "b2"],
                    "c12a", "c12b", "c12_in1_T2", "c12_in2_T2",
                )
                p.thus(body_T2).by_disj("c12d")
            # 13. In_a (binary recursive).
            with p.case(
                "c13: ?a1 a2 b1 b2. a = In_a a1 a2 /\\ b = In_a b1 b2 "
                "/\\ In (Pair_ord a1 b1) T1 /\\ In (Pair_ord a2 b2) T1"
            ):
                p.split("b2_eq", "(c13a, c13b, c13_in1, c13_in2)")
                p.have("c13_in1_T2: In (Pair_ord a1 b1) T2").by(
                    "hsub", "Pair_ord a1 b1", "c13_in1"
                )
                p.have("c13_in2_T2: In (Pair_ord a2 b2) T2").by(
                    "hsub", "Pair_ord a2 b2", "c13_in2"
                )
                p.have(
                    "c13d: ?a1 a2 b1 b2. a = In_a a1 a2 /\\ b = In_a b1 b2 "
                    "/\\ In (Pair_ord a1 b1) T2 /\\ In (Pair_ord a2 b2) T2"
                ).by_exists(
                    ["a1", "a2", "b1", "b2"],
                    "c13a", "c13b", "c13_in1_T2", "c13_in2_T2",
                )
                p.thus(body_T2).by_disj("c13d")

    p.thus("is_substitute_step T2 t v a b").by_rewrite_of(
        "hd2", [IS_SUBSTITUTE_STEP_AT]
    )


# ---------------------------------------------------------------------------
# Helpers for TRACE_EXISTS: membership growth and the generic extension
# lemma TRACE_EXTEND_BIN that combines two sub-trace validities with a
# fresh substitute step at (F, r) into a full ``is_substitute_trace``.
# ---------------------------------------------------------------------------


@proof
def IN_INSERT_GROW(p):
    """|- !i s x. In x s ==> In x (Insert i s).

    Membership is preserved by Insert. Case-split on ``i = x``:
    HIT collapses via IN_INSERT_SAME; MISS via IN_INSERT_DIFF.
    """
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
    p.have("h_eq: In x (Union a b) = (In x a \\/ In x b)").by(IN_UNION, "x", "a", "b")
    p.thus("In x (Union a b)").by_eq_mp("h_eq", "hd")


@proof
def IN_UNION_RIGHT(p):
    """|- !a b x. In x b ==> In x (Union a b)."""
    p.goal("!a b x. In x b ==> In x (Union a b)")
    p.fix("a b x")
    p.assume("hx: In x b")
    p.have("hd: In x a \\/ In x b").by_disj("hx")
    p.have("h_eq: In x (Union a b) = (In x a \\/ In x b)").by(IN_UNION, "x", "a", "b")
    p.thus("In x (Union a b)").by_eq_mp("h_eq", "hd")


# ---------------------------------------------------------------------------
# Phase 0 prototype for HF-native proof objects.
#
# These lemmas exercise the ranked-set proof-object design before any
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
        "/\\ nat0_lt i k /\\ nat0_lt j k /\\ is_mp f g h) "
        "\\/ (?i f. In (Pair_ord i f) P /\\ nat0_lt i k /\\ is_gen f h)"
    )
    bodyQ = (
        "is_axiom h "
        "\\/ (?i f j g. In (Pair_ord i f) Q /\\ In (Pair_ord j g) Q "
        "/\\ nat0_lt i k /\\ nat0_lt j k /\\ is_mp f g h) "
        "\\/ (?i f. In (Pair_ord i f) Q /\\ nat0_lt i k /\\ is_gen f h)"
    )
    p.have(f"bodyP: {bodyP}").by_eq_mp(atP, "vP")
    with p.cases_on("bodyP"):
        with p.case("ax: is_axiom h"):
            p.have(f"bodyQ: {bodyQ}").by_disj("ax")
            p.thus("valid_step_hf_set Q k h").by_eq_mp(SYM(atQ), "bodyQ")
        with p.case(
            "mpP: ?i f j g. In (Pair_ord i f) P /\\ In (Pair_ord j g) P "
            "/\\ nat0_lt i k /\\ nat0_lt j k /\\ is_mp f g h"
        ):
            p.split("g_eq", "(in_i_P, in_j_P, lt_i, lt_j, mp)")
            p.have("in_i_Q: In (Pair_ord i f) Q").by("sub", "Pair_ord i f", "in_i_P")
            p.have("in_j_Q: In (Pair_ord j g) Q").by("sub", "Pair_ord j g", "in_j_P")
            # DSL friction: by_exists wants each substituted conjunct as
            # a separate rule; passing a prebuilt conjunction is rejected.
            p.have(
                "mpQ: ?i f j g. In (Pair_ord i f) Q /\\ In (Pair_ord j g) Q "
                "/\\ nat0_lt i k /\\ nat0_lt j k /\\ is_mp f g h"
            ).by_exists(["i", "f", "j", "g"], "in_i_Q", "in_j_Q", "lt_i", "lt_j", "mp")
            p.have(f"bodyQ: {bodyQ}").by_disj("mpQ")
            p.thus("valid_step_hf_set Q k h").by_eq_mp(SYM(atQ), "bodyQ")
        with p.case("genP: ?i f. In (Pair_ord i f) P /\\ nat0_lt i k /\\ is_gen f h"):
            p.split("f_eq", "(in_i_P, lt_i, gen)")
            p.have("in_i_Q: In (Pair_ord i f) Q").by("sub", "Pair_ord i f", "in_i_P")
            p.have("genQ: ?i f. In (Pair_ord i f) Q /\\ nat0_lt i k /\\ is_gen f h").by_exists(
                ["i", "f"], "in_i_Q", "lt_i", "gen"
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

    P = "Insert (Pair_ord 0 m) Empty"
    p.have(f"in_head_eq: In (Pair_ord 0 m) ({P}) = T").by_rewrite([IN_INSERT_SAME])
    p.have(f"in_head: In (Pair_ord 0 m) ({P})").by_thm(EQT_ELIM(p.fact("in_head_eq")))

    with p.have(
        f"valid_all: !j h. In (Pair_ord j h) ({P}) ==> valid_step_hf_set ({P}) j h"
    ).proof():
        p.fix("j h")
        p.assume(f"hin: In (Pair_ord j h) ({P})")
        with p.cases_on(EXCLUDED_MIDDLE, "Pair_ord 0 m = Pair_ord j h"):
            with p.case("heq: Pair_ord 0 m = Pair_ord j h"):
                p.have("inj: 0 = j /\\ m = h").by(PAIR_ORD_INJ, "0", "m", "j", "h", "heq")
                p.split("inj", "(_j_eq, m_eq_h)")
                p.have("ax_h: is_axiom h").by_rewrite_of("ax", ["m_eq_h"])
                atP = SPECL([p._parse(P), p._parse("j"), p._parse("h")], VALID_STEP_HF_SET_AT)
                body = (
                    f"is_axiom h \\/ (?i f j0 g. In (Pair_ord i f) ({P}) "
                    f"/\\ In (Pair_ord j0 g) ({P}) /\\ nat0_lt i j "
                    f"/\\ nat0_lt j0 j /\\ is_mp f g h) "
                    f"\\/ (?i f. In (Pair_ord i f) ({P}) /\\ nat0_lt i j /\\ is_gen f h)"
                )
                p.have(f"vbody: {body}").by_disj("ax_h")
                p.thus(f"valid_step_hf_set ({P}) j h").by_eq_mp(SYM(atP), "vbody")
            with p.case("hne: ~(Pair_ord 0 m = Pair_ord j h)"):
                p.have(f"hin_empty_eq: In (Pair_ord j h) ({P}) = In (Pair_ord j h) Empty").by(
                    IN_INSERT_DIFF, "Pair_ord 0 m", "Pair_ord j h", "Empty", "hne"
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
    ).by_exists(["0"], "in_head", "valid_all")
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

    R = "Insert (Pair_ord (Pair_ord kf kg) g) (Union P Q)"
    kR = "Pair_ord kf kg"

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
                p.have(f"lt_f_rank: nat0_lt kf ({kR})").by(NAT0_LT_PAIR_ORD_L, "kf", "kg")
                p.have(f"lt_imp_rank: nat0_lt kg ({kR})").by(NAT0_LT_PAIR_ORD_R, "kf", "kg")
                p.have("lt_f_j: nat0_lt kf j").by_rewrite_of("lt_f_rank", ["rank_eq"])
                p.have("lt_imp_j: nat0_lt kg j").by_rewrite_of("lt_imp_rank", ["rank_eq"])
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
                    f"/\\ In (Pair_ord j0 g0) ({R}) /\\ nat0_lt i j "
                    f"/\\ nat0_lt j0 j /\\ is_mp f0 g0 h"
                ).by_exists(
                    ["kf", "f", "kg", "Imp_f f g"],
                    "in_f_R",
                    "in_imp_R",
                    "lt_f_j",
                    "lt_imp_j",
                    "mp_h",
                )
                atR = SPECL([p._parse(R), p._parse("j"), p._parse("h")], VALID_STEP_HF_SET_AT)
                body = (
                    f"is_axiom h \\/ (?i f0 j0 g0. In (Pair_ord i f0) ({R}) "
                    f"/\\ In (Pair_ord j0 g0) ({R}) /\\ nat0_lt i j "
                    f"/\\ nat0_lt j0 j /\\ is_mp f0 g0 h) "
                    f"\\/ (?i f0. In (Pair_ord i f0) ({R}) /\\ nat0_lt i j /\\ is_gen f0 h)"
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

    R = "Insert (Pair_ord (Pair_ord kf 0) (Forall_f x f)) P"
    kR = "Pair_ord kf 0"

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
                p.have(f"lt_f_rank: nat0_lt kf ({kR})").by(NAT0_LT_PAIR_ORD_L, "kf", "0")
                p.have("lt_f_j: nat0_lt kf j").by_rewrite_of("lt_f_rank", ["rank_eq"])
                p.have("gen_h: is_gen f h").by_rewrite_of("gen_fx", ["forall_eq_h"])
                p.have(
                    f"gen_ex: ?i f0. In (Pair_ord i f0) ({R}) "
                    f"/\\ nat0_lt i j /\\ is_gen f0 h"
                ).by_exists(["kf", "f"], "in_f_R", "lt_f_j", "gen_h")
                atR = SPECL([p._parse(R), p._parse("j"), p._parse("h")], VALID_STEP_HF_SET_AT)
                body = (
                    f"is_axiom h \\/ (?i f0 j0 g0. In (Pair_ord i f0) ({R}) "
                    f"/\\ In (Pair_ord j0 g0) ({R}) /\\ nat0_lt i j "
                    f"/\\ nat0_lt j0 j /\\ is_mp f0 g0 h) "
                    f"\\/ (?i f0. In (Pair_ord i f0) ({R}) /\\ nat0_lt i j /\\ is_gen f0 h)"
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
# Each closure rule now packages the corresponding HF-set proof-object
# prototype through ``PROV_HF_AT``. No list proof object, ``mem_l``, or
# ``append_l`` occurs in the ``Prov_HF`` route.
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
    """|- !f g. Prov_HF f /\\ Prov_HF (Imp_f f g) ==> Prov_HF g."""
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


# ---------------------------------------------------------------------------
# Stage 3B (l) -- the equivalence ``Prov_HF n <=> ?P. Proof_HF_set P n``.
#
# It is the set-native defining equation, packaged via ``PROV_HF_AT``.
# ---------------------------------------------------------------------------


PROV_HF_IFF_PROOF_HF_SET = PROV_HF_AT


@proof
def TRACE_EXTEND_BIN(p):
    """Generic trace extension.

    Given two sub-trace validities and an ``is_substitute_step`` for the
    headline pair (phi, r) at the merged trace, conclude the full
    ``is_substitute_trace`` at the merged trace
    ``T = Insert (Pair_ord phi r) (Union T1 T2)``.

    |- !phi r t v T1 T2.
         (!a b. In (Pair_ord a b) T1 ==> is_substitute_step T1 t v a b)
         ==> (!a b. In (Pair_ord a b) T2 ==> is_substitute_step T2 t v a b)
         ==> is_substitute_step (Insert (Pair_ord phi r) (Union T1 T2)) t v phi r
         ==> is_substitute_trace (Insert (Pair_ord phi r) (Union T1 T2)) phi t v r.

    The bound name ``phi`` is used (not ``F``) because the parser treats
    bare ``F`` as the boolean-false constant; identifiers visible after
    ``p.fix`` cannot shadow registered constants. Atomic cases use
    T1 = T2 = Empty (validities vacuous via NOT_IN_EMPTY); unary cases
    use T2 = Empty; binary cases use both. Lifts via TRACE_STEP_MONO
    with sub-trace inclusion ``T_i subseteq T``.
    """
    p.goal(
        "!phi r t v T1 T2. "
        "(!a b. In (Pair_ord a b) T1 ==> is_substitute_step T1 t v a b) "
        "==> (!a b. In (Pair_ord a b) T2 ==> is_substitute_step T2 t v a b) "
        "==> is_substitute_step (Insert (Pair_ord phi r) (Union T1 T2)) t v phi r "
        "==> is_substitute_trace (Insert (Pair_ord phi r) (Union T1 T2)) phi t v r"
    )
    p.fix("phi r t v T1 T2")
    p.assume("hv1: !a b. In (Pair_ord a b) T1 ==> is_substitute_step T1 t v a b")
    p.assume("hv2: !a b. In (Pair_ord a b) T2 ==> is_substitute_step T2 t v a b")
    p.assume(
        "hstep_phi: is_substitute_step "
        "(Insert (Pair_ord phi r) (Union T1 T2)) t v phi r"
    )

    # Membership growth: T1, T2 are subsets of the merged trace T.
    with p.have(
        "sub1: !x. In x T1 ==> In x (Insert (Pair_ord phi r) (Union T1 T2))"
    ).proof():
        p.fix("x")
        p.assume("hx: In x T1")
        p.have("h_un: In x (Union T1 T2)").by(IN_UNION_LEFT, "T1", "T2", "x", "hx")
        p.thus("In x (Insert (Pair_ord phi r) (Union T1 T2))").by(
            IN_INSERT_GROW, "Pair_ord phi r", "Union T1 T2", "x", "h_un"
        )
    with p.have(
        "sub2: !x. In x T2 ==> In x (Insert (Pair_ord phi r) (Union T1 T2))"
    ).proof():
        p.fix("x")
        p.assume("hx: In x T2")
        p.have("h_un: In x (Union T1 T2)").by(IN_UNION_RIGHT, "T1", "T2", "x", "hx")
        p.thus("In x (Insert (Pair_ord phi r) (Union T1 T2))").by(
            IN_INSERT_GROW, "Pair_ord phi r", "Union T1 T2", "x", "h_un"
        )

    # Validity for the merged trace.
    with p.have(
        "hvalid: !a b. In (Pair_ord a b) (Insert (Pair_ord phi r) (Union T1 T2)) "
        "==> is_substitute_step (Insert (Pair_ord phi r) (Union T1 T2)) t v a b"
    ).proof():
        p.fix("a b")
        p.assume(
            "hin: In (Pair_ord a b) (Insert (Pair_ord phi r) (Union T1 T2))"
        )
        with p.cases_on(EXCLUDED_MIDDLE, "Pair_ord phi r = Pair_ord a b"):
            with p.case("h_eq: Pair_ord phi r = Pair_ord a b"):
                p.have("h_inj: phi = a /\\ r = b").by(
                    PAIR_ORD_INJ, "phi", "r", "a", "b", "h_eq"
                )
                p.split("h_inj", "(hphia, hrb)")
                p.thus(
                    "is_substitute_step "
                    "(Insert (Pair_ord phi r) (Union T1 T2)) t v a b"
                ).by_rewrite_of("hstep_phi", ["hphia", "hrb"])
            with p.case("h_neq: ~(Pair_ord phi r = Pair_ord a b)"):
                p.have(
                    "h_diff: In (Pair_ord a b) "
                    "(Insert (Pair_ord phi r) (Union T1 T2)) "
                    "= In (Pair_ord a b) (Union T1 T2)"
                ).by(
                    IN_INSERT_DIFF,
                    "Pair_ord phi r",
                    "Pair_ord a b",
                    "Union T1 T2",
                    "h_neq",
                )
                p.have("h_in_union: In (Pair_ord a b) (Union T1 T2)").by_eq_mp(
                    "h_diff", "hin"
                )
                p.have(
                    "h_un_split: In (Pair_ord a b) T1 \\/ In (Pair_ord a b) T2"
                ).by_eq_mp(
                    SPECL(
                        [
                            p._parse("Pair_ord a b"),
                            p._parse("T1"),
                            p._parse("T2"),
                        ],
                        IN_UNION,
                    ),
                    "h_in_union",
                )
                with p.cases_on("h_un_split"):
                    with p.case("h1: In (Pair_ord a b) T1"):
                        p.have(
                            "hstep1: is_substitute_step T1 t v a b"
                        ).by("hv1", "a", "b", "h1")
                        p.thus(
                            "is_substitute_step "
                            "(Insert (Pair_ord phi r) (Union T1 T2)) t v a b"
                        ).by(
                            TRACE_STEP_MONO,
                            "T1",
                            "Insert (Pair_ord phi r) (Union T1 T2)",
                            "sub1",
                            "t",
                            "v",
                            "a",
                            "b",
                            "hstep1",
                        )
                    with p.case("h2: In (Pair_ord a b) T2"):
                        p.have(
                            "hstep2: is_substitute_step T2 t v a b"
                        ).by("hv2", "a", "b", "h2")
                        p.thus(
                            "is_substitute_step "
                            "(Insert (Pair_ord phi r) (Union T1 T2)) t v a b"
                        ).by(
                            TRACE_STEP_MONO,
                            "T2",
                            "Insert (Pair_ord phi r) (Union T1 T2)",
                            "sub2",
                            "t",
                            "v",
                            "a",
                            "b",
                            "hstep2",
                        )

    # Headline (1): In (Pair_ord phi r) T = T (IN_INSERT_SAME).
    from tactics import EQT_ELIM
    p.have(
        "hhead_eq: In (Pair_ord phi r) "
        "(Insert (Pair_ord phi r) (Union T1 T2)) = T"
    ).by_rewrite([IN_INSERT_SAME])
    p.have(
        "hhead: In (Pair_ord phi r) (Insert (Pair_ord phi r) (Union T1 T2))"
    ).by_thm(EQT_ELIM(p.fact("hhead_eq")))

    # Combine into the trace predicate via IS_SUBSTITUTE_TRACE_AT.
    p.have(
        "hbody: In (Pair_ord phi r) (Insert (Pair_ord phi r) (Union T1 T2)) /\\ "
        "(!a b. In (Pair_ord a b) (Insert (Pair_ord phi r) (Union T1 T2)) "
        "==> is_substitute_step (Insert (Pair_ord phi r) (Union T1 T2)) t v a b)"
    ).by_thm(CONJ(p.fact("hhead"), p.fact("hvalid")))
    p.thus(
        "is_substitute_trace (Insert (Pair_ord phi r) (Union T1 T2)) phi t v r"
    ).by_rewrite_of("hbody", [IS_SUBSTITUTE_TRACE_AT])


@proof
def EMPTY_TRACE_VALIDITY(p):
    """|- !t v a b. In (Pair_ord a b) Empty ==> is_substitute_step Empty t v a b.

    Vacuous: nothing is in Empty (NOT_IN_EMPTY). Used to instantiate the
    sub-trace validity hypotheses of ``TRACE_EXTEND_BIN`` when a slot is
    not actually recursed into (atomic cases set both T1 = T2 = Empty;
    unary cases set T2 = Empty).
    """
    p.goal(
        "!t v a b. In (Pair_ord a b) Empty ==> is_substitute_step Empty t v a b"
    )
    p.fix("t v a b")
    p.assume("hin: In (Pair_ord a b) Empty")
    p.have("hnin: ~In (Pair_ord a b) Empty").by(NOT_IN_EMPTY, "Pair_ord a b")
    p.absurd().by_conj("hin", "hnin")


# ---------------------------------------------------------------------------
# Per-case proof helpers for TRACE_EXISTS.
#
# Each helper is a plain Python function taking ``p`` (the active Proof)
# and the case-specific data; they call DSL primitives on ``p`` to build
# the headline ``is_substitute_step`` for the constructor case and close
# via ``TRACE_EXTEND_BIN``. The helpers expect the case to have already
# auto-introduced the constructor bvars; they perform the remaining
# ``p.choose`` and ``p.split`` steps.
# ---------------------------------------------------------------------------


def _ih_subtrace(p, sub_name, lt_label, term_label, sub_label):
    """Apply the strong-induction IH at sub-formula ``sub_name``, choose
    a sub-trace ``T_<sub_name>`` and split its body into headline /
    validity facts.

    Returns the (T_var, head_label, valid_label) trio of names registered.
    """
    p.have(
        f"{sub_label}_ex: ?T. is_substitute_trace T {sub_name} t v "
        f"(substitute {sub_name} t v)"
    ).by("IH", sub_name, lt_label, "t", "v", term_label)
    T_name = f"T_{sub_label}"
    p.choose(T_name, f"{sub_label}_ex", eq_label=f"{T_name}_eq")
    rec_T = SPECL(
        [
            p._parse(T_name),
            p._parse(sub_name),
            p._parse("t"),
            p._parse("v"),
            p._parse(f"substitute {sub_name} t v"),
        ],
        IS_SUBSTITUTE_TRACE_AT,
    )
    p.have(
        f"{T_name}_body: In (Pair_ord {sub_name} (substitute {sub_name} t v)) "
        f"{T_name} /\\ (!a b. In (Pair_ord a b) {T_name} "
        f"==> is_substitute_step {T_name} t v a b)"
    ).by_eq_mp(rec_T, f"{T_name}_eq")
    head_label = f"{T_name}_head"
    valid_label = f"{T_name}_valid"
    p.split(f"{T_name}_body", f"({head_label}, {valid_label})")
    return T_name, head_label, valid_label


def _membership_in_merged(p, sub_term, T_in, merged_str, source_label,
                          *, src_in_left, target_label):
    """Prove ``In sub_term merged_str`` from ``In sub_term T_in`` where
    merged_str = ``Insert (Pair_ord phi (substitute phi t v)) (Union T1 T2)``
    and ``T_in`` is either ``T1`` (src_in_left=True) or ``T2``."""
    grow_lemma = IN_UNION_LEFT if src_in_left else IN_UNION_RIGHT
    if src_in_left:
        un_args = [T_in, "Empty" if T_in.startswith("T1") and "T2" not in merged_str else _peer_of_left(merged_str), sub_term, source_label]
    # Simpler: just unwrap inline. (See _do_binary_*_case for direct calls.)
    raise NotImplementedError


def _peer_of_left(merged_str):
    return "<unused>"


def _do_binary_case(
    p, ctor, subst_at_lemma, lt_l_lemma, lt_r_lemma, step_body, *,
    sub_t_label="is_term", child_or="is_term"
):
    """Close a binary constructor case (Insert_t/Eq_f/Imp_f/In_a). The
    case has auto-introduced ``a`` and ``b`` and registered
    ``b_eq: phi = ctor a b /\\ <child_or> a /\\ <child_or> b``.

    ``child_or`` is the predicate guarding the children: ``is_term`` for
    Insert_t/Eq_f/In_a, ``is_form`` for Imp_f.
    """
    p.split("b_eq", "(phi_eq, h_a_pred, h_b_pred)")
    # Sub-formula nat0_lt facts.
    p.have(f"lt_a: nat0_lt a phi").by_rewrite_of(
        SPECL([p._parse("a"), p._parse("b")], lt_l_lemma), ["phi_eq"]
    )
    p.have(f"lt_b: nat0_lt b phi").by_rewrite_of(
        SPECL([p._parse("a"), p._parse("b")], lt_r_lemma), ["phi_eq"]
    )
    p.have(f"hor_a: is_term a \\/ is_form a").by_disj("h_a_pred")
    p.have(f"hor_b: is_term b \\/ is_form b").by_disj("h_b_pred")
    # IH on each child.
    _ih_subtrace(p, "a", "lt_a", "hor_a", "a")
    _ih_subtrace(p, "b", "lt_b", "hor_b", "b")
    # substitute phi t v = ctor (substitute a t v) (substitute b t v).
    p.have(
        f"h_subst: substitute phi t v "
        f"= {ctor} (substitute a t v) (substitute b t v)"
    ).by_rewrite(["phi_eq", subst_at_lemma])
    merged = (
        "Insert (Pair_ord phi (substitute phi t v)) (Union T_a T_b)"
    )
    # In (Pair_ord a (substitute a t v)) merged via T_a side.
    with p.have(
        f"h_in_a: In (Pair_ord a (substitute a t v)) ({merged})"
    ).proof():
        p.have(
            "h_in_un: In (Pair_ord a (substitute a t v)) (Union T_a T_b)"
        ).by(IN_UNION_LEFT, "T_a", "T_b",
             "Pair_ord a (substitute a t v)", "T_a_head")
        p.thus(
            f"In (Pair_ord a (substitute a t v)) ({merged})"
        ).by(IN_INSERT_GROW,
             "Pair_ord phi (substitute phi t v)",
             "Union T_a T_b",
             "Pair_ord a (substitute a t v)",
             "h_in_un")
    with p.have(
        f"h_in_b: In (Pair_ord b (substitute b t v)) ({merged})"
    ).proof():
        p.have(
            "h_in_un: In (Pair_ord b (substitute b t v)) (Union T_a T_b)"
        ).by(IN_UNION_RIGHT, "T_a", "T_b",
             "Pair_ord b (substitute b t v)", "T_b_head")
        p.thus(
            f"In (Pair_ord b (substitute b t v)) ({merged})"
        ).by(IN_INSERT_GROW,
             "Pair_ord phi (substitute phi t v)",
             "Union T_a T_b",
             "Pair_ord b (substitute b t v)",
             "h_in_un")
    # Build the constructor's disjunct's existential.
    p.have(
        f"h_disj_step: ?a1 a2 b1 b2. phi = {ctor} a1 a2 "
        f"/\\ substitute phi t v = {ctor} b1 b2 "
        f"/\\ In (Pair_ord a1 b1) ({merged}) "
        f"/\\ In (Pair_ord a2 b2) ({merged})"
    ).by_exists(
        ["a", "b", "substitute a t v", "substitute b t v"],
        "phi_eq", "h_subst", "h_in_a", "h_in_b",
    )
    p.have(f"h_body: {step_body(merged)}").by_disj("h_disj_step")
    p.have(
        f"h_step: is_substitute_step ({merged}) "
        f"t v phi (substitute phi t v)"
    ).by_rewrite_of("h_body", [IS_SUBSTITUTE_STEP_AT])
    p.have(
        f"h_trace: is_substitute_trace ({merged}) "
        f"phi t v (substitute phi t v)"
    ).by(
        TRACE_EXTEND_BIN,
        "phi", "substitute phi t v",
        "t", "v", "T_a", "T_b",
        "T_a_valid", "T_b_valid", "h_step",
    )
    p.thus(
        "?T. is_substitute_trace T phi t v (substitute phi t v)"
    ).by_witness(merged, "h_trace")


# Aliases for the term-children and form-children variants -- they share
# the same proof structure; ``is_term``/``is_form`` distinction matters
# only for the ``by_disj`` membership check, which uses the ``\/`` of
# both predicates and accepts either.
_do_binary_term_case = _do_binary_case
_do_binary_form_case = _do_binary_case


def _do_unary_form_case(p, ctor, subst_at_lemma, lt_lemma, step_body):
    """Close a unary constructor case (Not_f). Auto-introduced
    ``x`` plus ``x_eq: phi = ctor x /\\ <pred> x``."""
    p.split("x_eq", "(phi_eq, h_xp)")
    p.have(f"lt_x: nat0_lt x phi").by_rewrite_of(
        SPEC(p._parse("x"), lt_lemma), ["phi_eq"]
    )
    p.have(f"hor_x: is_term x \\/ is_form x").by_disj("h_xp")
    _ih_subtrace(p, "x", "lt_x", "hor_x", "x")
    p.have(
        f"h_subst: substitute phi t v = {ctor} (substitute x t v)"
    ).by_rewrite(["phi_eq", subst_at_lemma])
    merged = (
        "Insert (Pair_ord phi (substitute phi t v)) (Union T_x Empty)"
    )
    with p.have(
        f"h_in_sub: In (Pair_ord x (substitute x t v)) ({merged})"
    ).proof():
        p.have(
            "h_in_un: In (Pair_ord x (substitute x t v)) (Union T_x Empty)"
        ).by(IN_UNION_LEFT, "T_x", "Empty",
             "Pair_ord x (substitute x t v)", "T_x_head")
        p.thus(
            f"In (Pair_ord x (substitute x t v)) ({merged})"
        ).by(IN_INSERT_GROW,
             "Pair_ord phi (substitute phi t v)",
             "Union T_x Empty",
             "Pair_ord x (substitute x t v)",
             "h_in_un")
    p.have(
        f"h_disj_step: ?s1 s2. phi = {ctor} s1 "
        f"/\\ substitute phi t v = {ctor} s2 "
        f"/\\ In (Pair_ord s1 s2) ({merged})"
    ).by_exists(
        ["x", "substitute x t v"],
        "phi_eq", "h_subst", "h_in_sub",
    )
    p.have(f"h_body: {step_body(merged)}").by_disj("h_disj_step")
    p.have(
        f"h_step: is_substitute_step ({merged}) "
        f"t v phi (substitute phi t v)"
    ).by_rewrite_of("h_body", [IS_SUBSTITUTE_STEP_AT])
    p.have(
        f"h_trace: is_substitute_trace ({merged}) "
        f"phi t v (substitute phi t v)"
    ).by(
        TRACE_EXTEND_BIN,
        "phi", "substitute phi t v",
        "t", "v", "T_x", "Empty",
        "T_x_valid", "hev", "h_step",
    )
    p.thus(
        "?T. is_substitute_trace T phi t v (substitute phi t v)"
    ).by_witness(merged, "h_trace")


def _do_forall_case(p, step_body):
    """Close the Forall_f case with hit/miss split. Auto-introduced
    ``a`` and ``b`` plus ``b_eq: phi = Forall_f a b /\\ is_form b``."""
    p.split("b_eq", "(phi_eq, h_b_form)")
    with p.cases_on(EXCLUDED_MIDDLE, "a = v"):
        with p.case("hit: a = v"):
            # phi = Forall_f a b; a = v; substitute = phi (no-op).
            p.have("hit_sym: v = a").by_thm(SYM(p.fact("hit")))
            p.have(
                "h_subst_inner: substitute (Forall_f a b) t v = Forall_f a b"
            ).by(SUBSTITUTE_AT_FORALL_HIT, "a", "b", "t", "v", "hit_sym")
            p.have(
                "h_subst: substitute phi t v = phi"
            ).by_rewrite_of(
                "h_subst_inner",
                [SYM(p.fact("phi_eq"))],
            )
            # b (= substitute phi t v after rewrite) — express as Forall_f a b.
            p.have(
                "h_b_eq: substitute phi t v = Forall_f a b"
            ).by_rewrite_of("h_subst", ["phi_eq"])
            # Disjunct 10: ?w f1. a' = Forall_f w f1 /\ w = v /\ b' = Forall_f w f1.
            # Witness w=a, f1=b. (Note inner a, b don't conflict with outer
            # is_substitute_step's a, b which are different bvars.)
            p.have(
                "h_disj_step: ?w f1. phi = Forall_f w f1 "
                "/\\ w = v "
                "/\\ substitute phi t v = Forall_f w f1"
            ).by_exists(
                ["a", "b"], "phi_eq", "hit", "h_b_eq"
            )
            merged = (
                "Insert (Pair_ord phi (substitute phi t v)) "
                "(Union Empty Empty)"
            )
            p.have(f"h_body: {step_body(merged)}").by_disj("h_disj_step")
            p.have(
                f"h_step: is_substitute_step ({merged}) "
                f"t v phi (substitute phi t v)"
            ).by_rewrite_of("h_body", [IS_SUBSTITUTE_STEP_AT])
            p.have(
                f"h_trace: is_substitute_trace ({merged}) "
                f"phi t v (substitute phi t v)"
            ).by(
                TRACE_EXTEND_BIN,
                "phi", "substitute phi t v",
                "t", "v", "Empty", "Empty",
                "hev", "hev", "h_step",
            )
            p.thus(
                "?T. is_substitute_trace T phi t v (substitute phi t v)"
            ).by_witness(merged, "h_trace")
        with p.case("miss: ~(a = v)"):
            # phi = Forall_f a b; ~(a = v); recurse on b.
            with p.have("miss_sym: ~(v = a)").proof():
                with p.suppose("hva: v = a"):
                    p.have("hav: a = v").by_thm(SYM(p.fact("hva")))
                    p.absurd().by_conj("hav", "miss")
            p.have(
                "h_subst_inner: substitute (Forall_f a b) t v "
                "= Forall_f a (substitute b t v)"
            ).by(SUBSTITUTE_AT_FORALL_MISS, "a", "b", "t", "v", "miss_sym")
            p.have(
                "h_subst: substitute phi t v "
                "= Forall_f a (substitute b t v)"
            ).by_rewrite_of(
                "h_subst_inner",
                [SYM(p.fact("phi_eq"))],
            )
            p.have("lt_b: nat0_lt b phi").by_rewrite_of(
                SPECL([p._parse("a"), p._parse("b")], NAT0_LT_FORALL_F_R),
                ["phi_eq"],
            )
            p.have("hor_b: is_term b \\/ is_form b").by_disj("h_b_form")
            _ih_subtrace(p, "b", "lt_b", "hor_b", "b")
            merged = (
                "Insert (Pair_ord phi (substitute phi t v)) (Union T_b Empty)"
            )
            with p.have(
                f"h_in_b: In (Pair_ord b (substitute b t v)) ({merged})"
            ).proof():
                p.have(
                    "h_in_un: In (Pair_ord b (substitute b t v)) "
                    "(Union T_b Empty)"
                ).by(IN_UNION_LEFT, "T_b", "Empty",
                     "Pair_ord b (substitute b t v)", "T_b_head")
                p.thus(
                    f"In (Pair_ord b (substitute b t v)) ({merged})"
                ).by(IN_INSERT_GROW,
                     "Pair_ord phi (substitute phi t v)",
                     "Union T_b Empty",
                     "Pair_ord b (substitute b t v)",
                     "h_in_un")
            # Disjunct 11: ?w f1 f2. a' = Forall_f w f1 /\ ~(w=v)
            #                        /\ b' = Forall_f w f2 /\ In (Pair_ord f1 f2) T.
            # Witness w=a, f1=b, f2=substitute b t v.
            p.have(
                "h_disj_step: ?w f1 f2. phi = Forall_f w f1 "
                "/\\ ~(w = v) "
                "/\\ substitute phi t v = Forall_f w f2 "
                f"/\\ In (Pair_ord f1 f2) ({merged})"
            ).by_exists(
                ["a", "b", "substitute b t v"],
                "phi_eq", "miss", "h_subst", "h_in_b",
            )
            p.have(f"h_body: {step_body(merged)}").by_disj("h_disj_step")
            p.have(
                f"h_step: is_substitute_step ({merged}) "
                f"t v phi (substitute phi t v)"
            ).by_rewrite_of("h_body", [IS_SUBSTITUTE_STEP_AT])
            p.have(
                f"h_trace: is_substitute_trace ({merged}) "
                f"phi t v (substitute phi t v)"
            ).by(
                TRACE_EXTEND_BIN,
                "phi", "substitute phi t v",
                "t", "v", "T_b", "Empty",
                "T_b_valid", "hev", "h_step",
            )
            p.thus(
                "?T. is_substitute_trace T phi t v (substitute phi t v)"
            ).by_witness(merged, "h_trace")


# ---------------------------------------------------------------------------
# TRACE_EXISTS -- trace existence for syntactic F.
#
#   |- !F t v. (is_term F \/ is_form F) ==>
#               ?T. is_substitute_trace T F t v (substitute F t v).
#
# Strong induction on F via nat0_lt; case-split on the is_term / is_form
# disjuncts to expose F's constructor shape; in each constructor case
# build the trace as ``Insert (Pair_ord F (substitute F t v))
# (Union T_sub1 T_sub2)`` over IH-supplied sub-traces (with Empty
# fillers for atomic / unary cases), then close via TRACE_EXTEND_BIN.
# ---------------------------------------------------------------------------


@proof
def TRACE_EXISTS(p):
    # Bound variable named ``phi`` rather than ``F`` because the parser
    # resolves bare ``F`` to the boolean false constant (DEFAULT_SIG); a
    # fix'd Var would never shadow it. The theorem statement is otherwise
    # identical (alpha-equivalent under the outer forall).
    p.goal(
        "!phi t v. (is_term phi \\/ is_form phi) ==> "
        "?T. is_substitute_trace T phi t v (substitute phi t v)"
    )
    with p.strong_induction("phi", "IH"):
        # IH : !k. nat0_lt k phi
        #          ==> !t v. (is_term k \/ is_form k)
        #                    ==> ?T. is_substitute_trace T k t v (substitute k t v).
        p.fix("t v")
        p.assume("hphi: is_term phi \\/ is_form phi")

        # Empty validity (used by atomic / unary cases as filler).
        p.have(
            "hev: !a b. In (Pair_ord a b) Empty "
            "==> is_substitute_step Empty t v a b"
        ).by(EMPTY_TRACE_VALIDITY, "t", "v")

        # Helper: 9-disjunction body of is_substitute_step at the
        # headline pair (phi, substitute phi t v) -- i.e. the result of
        # applying IS_SUBSTITUTE_STEP_AT and substituting a := phi,
        # b := substitute phi t v.
        def step_body(T):
            A = "phi"
            B = "(substitute phi t v)"
            T = f"({T})"
            return (
                f"({A} = Empty_t /\\ {B} = Empty_t) "
                f"\\/ ({A} = Var_t v /\\ {B} = t) "
                f"\\/ (?w. {A} = Var_t w /\\ ~(w = v) /\\ {B} = Var_t w) "
                f"\\/ (?a1 a2 b1 b2. {A} = Eq_f a1 a2 /\\ {B} = Eq_f b1 b2 "
                f"      /\\ In (Pair_ord a1 b1) {T} /\\ In (Pair_ord a2 b2) {T}) "
                f"\\/ (?s1 s2. {A} = Not_f s1 /\\ {B} = Not_f s2 "
                f"      /\\ In (Pair_ord s1 s2) {T}) "
                f"\\/ (?a1 a2 b1 b2. {A} = Imp_f a1 a2 /\\ {B} = Imp_f b1 b2 "
                f"      /\\ In (Pair_ord a1 b1) {T} /\\ In (Pair_ord a2 b2) {T}) "
                f"\\/ (?w f1. {A} = Forall_f w f1 /\\ w = v /\\ {B} = Forall_f w f1) "
                f"\\/ (?w f1 f2. {A} = Forall_f w f1 /\\ ~(w = v) "
                f"      /\\ {B} = Forall_f w f2 /\\ In (Pair_ord f1 f2) {T}) "
                f"\\/ (?a1 a2 b1 b2. {A} = Insert_t a1 a2 /\\ {B} = Insert_t b1 b2 "
                f"      /\\ In (Pair_ord a1 b1) {T} /\\ In (Pair_ord a2 b2) {T}) "
                f"\\/ (?a1 a2 b1 b2. {A} = In_a a1 a2 /\\ {B} = In_a b1 b2 "
                f"      /\\ In (Pair_ord a1 b1) {T} /\\ In (Pair_ord a2 b2) {T})"
            )

        with p.cases_on("hphi"):
            # =========================================================
            # CASE: is_term phi.
            # =========================================================
            with p.case("ht: is_term phi"):
                ht_disj_str = (
                    "phi = Empty_t "
                    "\\/ (?x. phi = Var_t x) "
                    "\\/ (?a b. phi = Insert_t a b /\\ is_term a /\\ is_term b)"
                )
                rec_at_phi = SPEC(p._parse("phi"), IS_TERM_REC)
                p.have(f"ht_disj: {ht_disj_str}").by_eq_mp(rec_at_phi, "ht")

                with p.cases_on("ht_disj"):
                    # --- Empty_t ---
                    with p.case("c_empty: phi = Empty_t"):
                        merged = (
                            "Insert (Pair_ord phi (substitute phi t v)) "
                            "(Union Empty Empty)"
                        )
                        # substitute phi t v = Empty_t.
                        p.have(
                            "h_subst: substitute phi t v = Empty_t"
                        ).by_rewrite(["c_empty", SUBSTITUTE_AT_EMPTY])
                        # Disjunct 1: phi = Empty_t /\ substitute phi t v = Empty_t.
                        p.have(
                            "h_clause: phi = Empty_t "
                            "/\\ substitute phi t v = Empty_t"
                        ).by_thm(CONJ(p.fact("c_empty"), p.fact("h_subst")))
                        # by_disj on a conjunction-typed leaf works -- the
                        # disjunction's leaf is exactly this conjunction.
                        p.have(
                            f"h_body: {step_body(merged)}"
                        ).by_disj("h_clause")
                        p.have(
                            f"h_step: is_substitute_step ({merged}) "
                            f"t v phi (substitute phi t v)"
                        ).by_rewrite_of("h_body", [IS_SUBSTITUTE_STEP_AT])
                        p.have(
                            f"h_trace: is_substitute_trace ({merged}) "
                            f"phi t v (substitute phi t v)"
                        ).by(
                            TRACE_EXTEND_BIN,
                            "phi", "substitute phi t v",
                            "t", "v", "Empty", "Empty",
                            "hev", "hev", "h_step",
                        )
                        p.thus(
                            "?T. is_substitute_trace T phi t v (substitute phi t v)"
                        ).by_witness(merged, "h_trace")

                    # --- Var_t (atomic; hit/miss split) ---
                    with p.case("c_var: ?x. phi = Var_t x"):
                        # Auto-chooses x; x_eq: phi = Var_t x.
                        merged = (
                            "Insert (Pair_ord phi (substitute phi t v)) "
                            "(Union Empty Empty)"
                        )
                        with p.cases_on(EXCLUDED_MIDDLE, "v = x"):
                            with p.case("hit: v = x"):
                                # phi = Var_t x = Var_t v; substitute = t.
                                p.have(
                                    "h_subst_inner: substitute (Var_t x) t v = t"
                                ).by(SUBSTITUTE_AT_VAR_HIT, "x", "t", "v", "hit")
                                p.have(
                                    "h_subst: substitute phi t v = t"
                                ).by_rewrite_of(
                                    "h_subst_inner", [SYM(p.fact("x_eq"))]
                                )
                                # phi = Var_t v.
                                p.have("h_xv: x = v").by_thm(
                                    SYM(p.fact("hit"))
                                )
                                p.have("h_phi_var_v: phi = Var_t v").by_rewrite_of(
                                    "x_eq", ["h_xv"]
                                )
                                # Disjunct 3: a = Var_t v /\ b = t.
                                p.have(
                                    "h_clause: phi = Var_t v "
                                    "/\\ substitute phi t v = t"
                                ).by_thm(
                                    CONJ(p.fact("h_phi_var_v"), p.fact("h_subst"))
                                )
                                p.have(
                                    f"h_body: {step_body(merged)}"
                                ).by_disj("h_clause")
                                p.have(
                                    f"h_step: is_substitute_step ({merged}) "
                                    f"t v phi (substitute phi t v)"
                                ).by_rewrite_of(
                                    "h_body", [IS_SUBSTITUTE_STEP_AT]
                                )
                                p.have(
                                    f"h_trace: is_substitute_trace ({merged}) "
                                    f"phi t v (substitute phi t v)"
                                ).by(
                                    TRACE_EXTEND_BIN,
                                    "phi", "substitute phi t v",
                                    "t", "v", "Empty", "Empty",
                                    "hev", "hev", "h_step",
                                )
                                p.thus(
                                    "?T. is_substitute_trace T phi t v "
                                    "(substitute phi t v)"
                                ).by_witness(merged, "h_trace")
                            with p.case("miss: ~(v = x)"):
                                # phi = Var_t x; ~(v = x).
                                # substitute (Var_t x) t v = Var_t x = phi.
                                p.have(
                                    "h_subst_x: substitute (Var_t x) t v = Var_t x"
                                ).by(
                                    SUBSTITUTE_AT_VAR_MISS, "x", "t", "v", "miss"
                                )
                                p.have(
                                    "h_subst: substitute phi t v = phi"
                                ).by_rewrite_of(
                                    "h_subst_x",
                                    [SYM(p.fact("x_eq"))],
                                )
                                # Need ~(x = v) for the disjunct (NEQ_SYM).
                                with p.have("h_xv_neq: ~(x = v)").proof():
                                    with p.suppose("hxv: x = v"):
                                        p.have("hvx: v = x").by_thm(
                                            SYM(p.fact("hxv"))
                                        )
                                        p.absurd().by_conj("hvx", "miss")
                                # Disjunct 4: ?w. a=Var_t w /\ ~(w=v) /\ b=Var_t w.
                                # Witness w = x; b = Var_t x = phi (= substitute phi t v).
                                p.have(
                                    "h_b_eq: substitute phi t v = Var_t x"
                                ).by_rewrite_of(
                                    "h_subst", ["x_eq"],
                                )
                                p.have(
                                    "h_disj_step: ?w. phi = Var_t w "
                                    "/\\ ~(w = v) "
                                    "/\\ substitute phi t v = Var_t w"
                                ).by_exists(
                                    ["x"], "x_eq", "h_xv_neq", "h_b_eq",
                                )
                                p.have(
                                    f"h_body: {step_body(merged)}"
                                ).by_disj("h_disj_step")
                                p.have(
                                    f"h_step: is_substitute_step ({merged}) "
                                    f"t v phi (substitute phi t v)"
                                ).by_rewrite_of(
                                    "h_body", [IS_SUBSTITUTE_STEP_AT]
                                )
                                p.have(
                                    f"h_trace: is_substitute_trace ({merged}) "
                                    f"phi t v (substitute phi t v)"
                                ).by(
                                    TRACE_EXTEND_BIN,
                                    "phi", "substitute phi t v",
                                    "t", "v", "Empty", "Empty",
                                    "hev", "hev", "h_step",
                                )
                                p.thus(
                                    "?T. is_substitute_trace T phi t v "
                                    "(substitute phi t v)"
                                ).by_witness(merged, "h_trace")

                    # --- Insert_t (binary) ---
                    with p.case(
                        "c_insert: ?a b. phi = Insert_t a b "
                        "/\\ is_term a /\\ is_term b"
                    ):
                        _do_binary_term_case(
                            p, "Insert_t", SUBSTITUTE_AT_INSERT,
                            NAT0_LT_INSERT_T_L, NAT0_LT_INSERT_T_R, step_body,
                        )

            # =========================================================
            # CASE: is_form phi.
            # =========================================================
            with p.case("hf: is_form phi"):
                hf_disj_str = (
                    "(?a b. phi = Eq_f a b /\\ is_term a /\\ is_term b) "
                    "\\/ (?x. phi = Not_f x /\\ is_form x) "
                    "\\/ (?a b. phi = Imp_f a b /\\ is_form a /\\ is_form b) "
                    "\\/ (?a b. phi = Forall_f a b /\\ is_form b) "
                    "\\/ (?a b. phi = In_a a b /\\ is_term a /\\ is_term b)"
                )
                rec_at_phi_form = SPEC(p._parse("phi"), IS_FORM_REC)
                p.have(f"hf_disj: {hf_disj_str}").by_eq_mp(rec_at_phi_form, "hf")

                with p.cases_on("hf_disj"):
                    with p.case(
                        "c_eq: ?a b. phi = Eq_f a b "
                        "/\\ is_term a /\\ is_term b"
                    ):
                        _do_binary_term_case(
                            p, "Eq_f", SUBSTITUTE_AT_EQ,
                            NAT0_LT_EQ_F_L, NAT0_LT_EQ_F_R, step_body,
                        )
                    with p.case("c_not: ?x. phi = Not_f x /\\ is_form x"):
                        _do_unary_form_case(
                            p, "Not_f", SUBSTITUTE_AT_NOT,
                            NAT0_LT_NOT_F, step_body,
                        )
                    with p.case(
                        "c_imp: ?a b. phi = Imp_f a b "
                        "/\\ is_form a /\\ is_form b"
                    ):
                        _do_binary_form_case(
                            p, "Imp_f", SUBSTITUTE_AT_IMP,
                            NAT0_LT_IMP_F_L, NAT0_LT_IMP_F_R, step_body,
                        )
                    with p.case(
                        "c_fa: ?a b. phi = Forall_f a b /\\ is_form b"
                    ):
                        _do_forall_case(p, step_body)
                    with p.case(
                        "c_in: ?a b. phi = In_a a b "
                        "/\\ is_term a /\\ is_term b"
                    ):
                        _do_binary_term_case(
                            p, "In_a", SUBSTITUTE_AT_IN,
                            NAT0_LT_IN_A_L, NAT0_LT_IN_A_R, step_body,
                        )


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
#   The ``SUBSTITUTE_REPRESENTS`` headline keeps ``numeral`` for the F /
#   t / v / r slots; the IS_*_REPRESENTS lemmas use ``quote_hf``
#   throughout since their inputs are all HF-shaped (traces, encoded
#   shapes, set members).
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
    is_axiom_th = EQ_MP(SYM(is_axiom_at), DISJ2(q_hf_part, is_logical_th))
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
# Needed for the trace HF set: the trace consists of Pair_ord-encoded
# (sub-shape, output-shape) entries, and HF must prove each entry's shape
# at numerals.
#
# Body: faithful equational encoding of the Kuratowski pair shape --
# ``var_z = {{var_x}, {var_x, var_y}}`` written out at the HF-syntax
# level using only ``Insert_t`` and ``Empty_t``:
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
# explicitly; downstream consumers (``IS_SUBSTITUTE_STEP_REPRESENTS``,
# etc.) will instantiate it at concrete numerals where the order is
# easily established.
IS_PAIR_ORD_INTERNAL_DEF = define(
    "is_Pair_ord_internal",
    nat0_ty,
    "Eq_f var_z "
    "(Insert_t (Insert_t var_x Empty_t) "
    "          (Insert_t "
    "             (Insert_t var_x (Insert_t var_y Empty_t)) "
    "             Empty_t))",
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
# Needed by every disjunct of is_substitute_step (which references
# ``In (Pair_ord _ _) T``) and by is_substitute_trace clause (i).
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


# IS_IN_REPRESENTS, IS_SUBSTITUTE_STEP_REPRESENTS,
# IS_SUBSTITUTE_TRACE_REPRESENTS, SUBSTITUTE_REPRESENTS,
# PROV_HF_REPRESENTS, IS_FORM_PROV_HF_INTERNAL, FREE_IN_PROV_HF_INTERNAL
# all live in ``hf_repr_thms.py`` (the high layer). Their proofs need
# the Prov_HF logical toolkit from ``hf_logic`` (PROV_HF_UI etc.), and
# ``hf_logic`` already imports this module -- inlining them here would
# cycle. The kernel constants and ``define``s those proofs reference
# (``is_*_internal``, ``Prov_HF_internal``, ``substitute_internal``,
# ``substitute_2``) stay here so the parser can resolve their names
# regardless of load order.


# B1.1 -- HF-encoding of is_substitute_step.
# 9-disjunct HF-formula matching the HOL ``is_substitute_step``. Free
# vars: var_T (trace), var_y (t), var_z (v), var_a (a), var_b (b).
# Composes IS_PAIR_ORD_REPRESENTS + IS_IN_REPRESENTS for the In-checks
# inside each recursive disjunct.
new_constant("is_substitute_step_internal", nat0_ty)
is_substitute_step_internal = mk_const("is_substitute_step_internal", [])


# IS_SUBSTITUTE_STEP_REPRESENTS body lives in hf_repr_thms.py.


# B1.2 -- HF-encoding of is_substitute_trace.
# Free vars: var_T (trace), var_x (F), var_y (t), var_z (v), var_w (r).
# Body: the conjunction
#   In (Pair_ord var_x var_w) var_T
#   /\ (Forall_f var_a (Forall_f var_b
#         (In (Pair_ord var_a var_b) var_T ==>
#          is_substitute_step_internal[var_T, var_y, var_z, var_a, var_b])))
# at the HF level. The single bound-variable forall is over (var_a, var_b),
# matching the HOL definition's ``!a b. ...``.
new_constant("is_substitute_trace_internal", nat0_ty)
is_substitute_trace_internal = mk_const("is_substitute_trace_internal", [])


# IS_SUBSTITUTE_TRACE_REPRESENTS body lives in hf_repr_thms.py.


# Opaque: no defining body. Defined elsewhere as the Sigma_1
# substitute-trace formula ``?T. is_substitute_trace_internal T F t v r``.
new_constant("substitute_internal", nat0_ty)
substitute_internal = mk_const("substitute_internal", [])


# SUBSTITUTE_REPRESENTS body lives in hf_repr_thms.py.


# ---------------------------------------------------------------------------
# Stage 3D (a) -- kernel symbol declarations for the provability
# representability headline (PROV_HF_REPRESENTS) and the diagonal
# lemma's side conditions.
#
# This file only declares the kernel constants
# (``Prov_HF_internal``, opaque) and the HOL helper
# (``substitute_2``). The theorems that mention them
# (PROV_HF_REPRESENTS, IS_FORM_PROV_HF_INTERNAL,
# FREE_IN_PROV_HF_INTERNAL), along with the construction strategy
# and discharge sketch, live in ``hf_repr_thms.py`` (the high
# layer, where the Prov_HF logical toolkit from ``hf_logic`` is in
# scope).
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


# Opaque: no defining body. Stage 3D will replace this with the
# bottom-up construction (Proof_HF_internal then existential closure).
new_constant("Prov_HF_internal", nat0_ty)
Prov_HF_internal = mk_const("Prov_HF_internal", [])


# PROV_HF_REPRESENTS, IS_FORM_PROV_HF_INTERNAL, FREE_IN_PROV_HF_INTERNAL
# bodies all live in hf_repr_thms.py.


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
    print("Stage 3B (set-native target) -- ranked HF-set proof objects.")
    print("    VALID_STEP_HF_SET_DEF       :", pp_thm(VALID_STEP_HF_SET_DEF))
    print("    VALID_STEP_HF_SET_AT        :", pp_thm(VALID_STEP_HF_SET_AT))
    print("    PROOF_HF_SET_DEF            :", pp_thm(PROOF_HF_SET_DEF))
    print("    PROOF_HF_SET_AT             :", pp_thm(PROOF_HF_SET_AT))
    print("    VALID_STEP_HF_SET_PRESERVES :", pp_thm(VALID_STEP_HF_SET_PRESERVES))
    print("    AXIOM_HAS_PROOF_HF_SET      :", pp_thm(AXIOM_HAS_PROOF_HF_SET))
    print("    MP_HAS_PROOF_HF_SET         :", pp_thm(MP_HAS_PROOF_HF_SET))
    print("    GEN_HAS_PROOF_HF_SET        :", pp_thm(GEN_HAS_PROOF_HF_SET))
    print()
    print("Stage 3B (a) -- list membership ``mem_l``.")
    print("    MEM_L_DEF       :", pp_thm(MEM_L_DEF))
    print("    MEM_L_REC       :", pp_thm(MEM_L_REC))
    print("    MEM_L_REC_PW    :", pp_thm(MEM_L_REC_PW))
    print("    MEM_L_AT_NIL    :", pp_thm(MEM_L_AT_NIL))
    print("    MEM_L_AT_CONS   :", pp_thm(MEM_L_AT_CONS))
    print()
    print("Stage 3B (b) -- valid_step.")
    print("    VALID_STEP_DEF :", pp_thm(VALID_STEP_DEF))
    print("    VALID_STEP_AT  :", pp_thm(VALID_STEP_AT))
    print()
    print("Stage 3B (c) -- list-based Proof_HF.")
    print("    PROOF_HF_DEF      :", pp_thm(PROOF_HF_DEF))
    print("    PROOF_HF_REC      :", pp_thm(PROOF_HF_REC))
    print("    PROOF_HF_REC_PW   :", pp_thm(PROOF_HF_REC_PW))
    print("    PROOF_HF_AT_NIL   :", pp_thm(PROOF_HF_AT_NIL))
    print("    PROOF_HF_AT_CONS  :", pp_thm(PROOF_HF_AT_CONS))
    print()
    print("Stage 3B (d) -- list concatenation append_l.")
    print("    APPEND_L_DEF     :", pp_thm(APPEND_L_DEF))
    print("    APPEND_L_REC     :", pp_thm(APPEND_L_REC))
    print("    APPEND_L_AT_NIL  :", pp_thm(APPEND_L_AT_NIL))
    print("    APPEND_L_AT_CONS :", pp_thm(APPEND_L_AT_CONS))
    print()
    print("Stage 3B (e-g) -- legacy list preservation lemmas.")
    print("    MEM_L_APPEND_PRESERVES :", pp_thm(MEM_L_APPEND_PRESERVES))
    print("    VALID_STEP_PRESERVES   :", pp_thm(VALID_STEP_PRESERVES))
    print("    PROOF_HF_APPEND         :", pp_thm(PROOF_HF_APPEND))
    print("    PROOF_HF_HEAD_MEM       :", pp_thm(PROOF_HF_HEAD_MEM))
    print()
    print("Stage 3B (i) -- legacy list proof witnesses.")
    print("    AXIOM_HAS_PROOF   :", pp_thm(AXIOM_HAS_PROOF))
    print("    GEN_HAS_PROOF     :", pp_thm(GEN_HAS_PROOF))
    print("    MP_HAS_PROOF      :", pp_thm(MP_HAS_PROOF))
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
    print("    IS_SUBSTITUTE_STEP_DEF :", pp_thm(IS_SUBSTITUTE_STEP_DEF))
    print("    IS_SUBSTITUTE_STEP_AT  : <9-disjunct body>")
    print("    IS_SUBSTITUTE_TRACE_DEF:", pp_thm(IS_SUBSTITUTE_TRACE_DEF))
    print("    IS_SUBSTITUTE_TRACE_AT :", pp_thm(IS_SUBSTITUTE_TRACE_AT))
    print("    TRACE_STEP_MONO                       :", pp_thm(TRACE_STEP_MONO))
    print("    TRACE_EXISTS                          :", pp_thm(TRACE_EXISTS))
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
        "    (Stage 3 high-layer reps -- IS_IN_REPRESENTS,",
        "IS_SUBSTITUTE_*_REPRESENTS,",
    )
    print("     PROV_HF_REPRESENTS, IS_FORM_PROV_HF_INTERNAL,")
    print("     FREE_IN_PROV_HF_INTERNAL -- live in hf_repr_thms.py.)")
    print()
    print("Stage 3D (a) -- substitute_2 helper (used by diagonal lemma).")
    print("    SUBSTITUTE_2_DEF        :", pp_thm(SUBSTITUTE_2_DEF))
