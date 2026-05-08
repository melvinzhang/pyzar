# ---------------------------------------------------------------------------
# Stage 3 -- representability of primitive recursive functions in Q.
# ---------------------------------------------------------------------------
#
# A predicate P : nat0 -> bool is *represented* in Q by a Q-formula
# F(x) -- with var_x as its sole free variable -- iff
#
#     |- !n. P n      ==> Prov_Q (substitute F (numeral n) var_x)
#     |- !n. ~ P n    ==> Prov_Q (Not_f (substitute F (numeral n) var_x))
#
# A function f : nat0 -> nat0 is represented by a Q-formula F(x, y) iff
#
#     |- !n. Prov_Q (substitute_2 F (numeral n) (numeral (f n)) var_x var_y)
#     |- !n. Prov_Q (Forall_f var_y
#                      (Imp_f (substitute_2 F (numeral n) y var_x var_y)
#                             (Eq_f y (numeral (f n))))).
#
# Theorem (representability). Every primitive recursive predicate /
# function on nat0 is representable in Q.
#
# This is the headline weak-arithmetic result. The standard proof
# (Boolos-Burgess-Jeffrey, "Computability and Logic" Ch. 16-17) goes:
#
#   * Constants, projections, successor, addition, multiplication --
#     direct unfolding against axioms Q4-Q7.
#   * Composition -- substitution; routine.
#   * Primitive recursion -- normally where induction enters. Q has no
#     induction schema, so we use Goedel's beta function: a fixed
#     ternary arithmetic predicate beta(a, b, i, y) such that for any
#     finite sequence (y_0, ..., y_k), there exist a, b with
#     beta(a, b, i, y_i) for each i. Construction via Chinese
#     remainder; existence is a numeric calculation that Q proves for
#     each numeral instance.
#
# In our HOL setting we don't need the full primitive recursion result
# -- we only need representability of three specific predicates:
#
#   (i)   ``Proof_Q``     (decidable, hence representable; the
#                          formula is an explicit bounded-quantifier
#                          encoding of the proof-checking procedure).
#   (ii)  ``substitute``  (primitive recursive on godelnums).
#   (iii) ``godelnum``    (degenerate -- just identity on encoded syntax;
#                          its numeral image is what matters).
#
# Each of these is several pages in textbook treatments. The slick HOL
# move is to define the representing formulas *by* the HOL definitions,
# transport through the bounded-quantifier translation, and then show
# by induction (in the *meta*theory; HOL has it) on syntactic
# complexity that Q proves the right characterisations. ~500 lines
# with the beta-function lemma factored out.
#
# (No saving here over PA: representability is exactly as hard with
# induction as without it; the beta-function trick was invented
# precisely so that the proof would not depend on induction. The
# saving over PA was at Stage 2.)
#
# ------------------------------------------------------------------
# Reconciliation with Stage 2's ``Prov_Q``:
# ------------------------------------------------------------------
#
# Stage 2 defines ``Prov_Q`` via impredicative intersection
# (``q_proof.PROV_Q_DEF``), not via an explicit list-based
# ``Proof_Q``. The two are HOL-equivalent (Knaster-Tarski) but the
# representability proof needs the list-based form: the diagonal
# lemma's ``Prov_Q_internal`` formula must internalise *explicit*
# proofs into Q's own language, so we want a Sigma_1 formula
# ``Proof_Q_internal`` saying "p is a list of formulas, each an axiom
# or following from earlier ones by MP/Gen, ending in n".
#
# Stage 3 therefore:
#   (a) Builds the list-based ``Proof_Q`` predicate (HOL function)
#       and proves ``Prov_Q n <=> ?p. Proof_Q p n`` against the
#       Stage-2 ``Prov_Q``.
#   (b) Defines ``Proof_Q_internal`` and ``Prov_Q_internal`` as
#       Q-formulas.
#   (c) Proves the representability theorem
#         |- !n. Prov_Q n <=> Prov_Q (godelnum (Prov_Q_internal (numeral n))).
#
# ------------------------------------------------------------------
# Output (eventual):
# ------------------------------------------------------------------
#
#   defn:  numeral : nat0 -> nat0
#          (numeral n = Succ_t^n Zero_t -- the n'th Q numeral)
#   defn:  represents_pred : nat0 -> (nat0 -> bool) -> bool
#   defn:  represents_func : nat0 -> (nat0 -> nat0) -> bool
#   defn:  Proof_Q         : nat0 -> nat0 -> bool
#   thm:   |- !n. Prov_Q n <=> ?p. Proof_Q p n
#   defn:  Proof_Q_internal, Prov_Q_internal : nat0 (Q-formulas)
#   thm:   |- !n. Prov_Q n <=>
#                Prov_Q (godelnum (Prov_Q_internal (numeral n)))
#
# ------------------------------------------------------------------
# This file (Stage 3A): foundations.
# ------------------------------------------------------------------
#
#   * ``numeral`` defined via ``define_unary_0``.
#   * ``IS_TERM_NUMERAL``: every numeral is a well-formed Q term.
#   * ``represents_pred``: representability of a unary nat0-predicate.
#
# Stage 3B (deferred): list-based ``Proof_Q``, the Prov_Q ↔
# ?p. Proof_Q p n equivalence, representability of ``substitute``.
#
# Stage 3C (deferred): ``Prov_Q_internal`` and the headline
# representability theorem.

# ---------------------------------------------------------------------------
# Imports.
# ---------------------------------------------------------------------------

from fusion import Var
from basics import mk_const, mk_app, mk_abs, rand, rator
from parser import define, parse_type
from axioms import mk_forall, mk_imp, mk_not, mk_and, mk_or, mk_exists
from nat0 import nat0_ty, define_unary_0
from nat0_order import define_wf_lt
from proof import proof
from tactics import (
    SPEC, SPECL, GEN, GENL, SYM, AP_THM, BETA_CONV, TRANS, DISJ1, DISJ2, REFL,
    EQ_MP, MP, CONJ, CONJUNCT1, CONJUNCT2, EXISTS, FUN_EXT, NOT_INTRO, DISCH,
    NOT_ELIM, EQF_INTRO, EQF_ELIM, CONTR,
)
from fusion import ASSUME, ABS
from basics import mk_eq

from q_syntax import (
    Zero_t, Succ_t,
    is_term_const,
    IS_TERM_REC, IS_TERM_AT_SUCC,
    mono_iff_eq_or_pw_step,
    _unfold_rec_via_F_def,
    _extract_nfg,
)
from axioms import dest_exists
from tactics import (
    CHOOSE_WITNESS, AP_TERM, OR_CONG, REWRITE_RULE,
)
from fusion import vsubst, aty, DEDUCT_ANTISYM_RULE
from q_proof import (
    var_x,
    Prov_Q,
    nil_l, cons_l, NIL_L_DEF, CONS_L_AT, CONS_L_INJ, CONS_L_NEQ_NIL,
    NAT0_LT_CONS_L_TAIL,
    is_axiom, is_mp, is_gen,
)


# ---------------------------------------------------------------------------
# Stage 3A (a) -- the numeral function.
#
#   numeral 0          =  Zero_t.
#   numeral (SUC0 n)   =  Succ_t (numeral n).
#
# Defined by primitive recursion on nat0 via ``define_unary_0``. The
# resulting term ``numeral n`` is a closed Q-term encoding the n'th
# successor of Zero (i.e. the standard von Neumann numeral encoded
# through Stage 1's term constructors).
# ---------------------------------------------------------------------------


_n_n0 = Var("n", nat0_ty)
_a_n0 = Var("a", nat0_ty)


# Step body: \k a. Succ_t a.  (k unused; the new value is just Succ_t
# applied to the recursive result.)
_h_numeral = mk_abs(_n_n0, mk_abs(_a_n0, mk_app(Succ_t, _a_n0)))


NUMERAL_BASE, NUMERAL_STEP = define_unary_0(
    "numeral",
    parse_type("nat0 -> nat0"),
    Zero_t,
    _h_numeral,
    result_ty=nat0_ty,
)
numeral = mk_const("numeral", [])


# ---------------------------------------------------------------------------
# Stage 3A (b) -- IS_TERM_NUMERAL: every numeral is a well-formed Q term.
#
#   |- !n. is_term (numeral n).
#
# Direct induction on n. The base case is a single application of
# IS_TERM_REC at Zero_t (the leftmost disjunct collapses to REFL).
# The step case uses IS_TERM_AT_SUCC (the Succ_t-recursion equation
# from Stage 1) with witness ``numeral n`` and the inductive
# hypothesis.
# ---------------------------------------------------------------------------


is_term = is_term_const  # parser-friendly alias


@proof
def IS_TERM_ZERO(p):
    """|- is_term Zero_t.

    From IS_TERM_REC at Zero_t, the body's leftmost disjunct
    ``Zero_t = Zero_t`` is reflexive; lift to the iff RHS by DISJ1
    and EQ_MP through SYM.
    """
    p.goal("is_term Zero_t")

    rec_at_zero = SPEC(Zero_t, IS_TERM_REC)
    # rec_at_zero : |- is_term Zero_t = (Zero_t = Zero_t \/ ...rest)
    rhs = rand(rec_at_zero._concl)
    # rhs has shape: (Zero_t = Zero_t) \/ rest
    refl_zero = REFL(Zero_t)  # |- Zero_t = Zero_t
    from basics import rand as _rand, rator as _rator
    # Extract the right disjunct of rhs.
    # rhs is ((Zero_t = Zero_t) \/ rest); its rator is `Or (Zero_t=Zero_t)`,
    # its rand is `rest`.
    rest = _rand(rhs)
    rhs_th = DISJ1(refl_zero, rest)  # |- (Zero_t = Zero_t) \/ rest
    p.thus("is_term Zero_t").by_eq_mp(SYM(rec_at_zero), rhs_th)


@proof
def IS_TERM_SUCC(p):
    """|- !t. is_term t ==> is_term (Succ_t t).

    ``IS_TERM_AT_SUCC`` from Stage 1 already simplifies the
    Succ-disjunct of the body to the bare ``is_term t``: |- !t.
    is_term (Succ_t t) = is_term t. So this lemma is one EQ_MP step.
    """
    p.goal("!t. is_term t ==> is_term (Succ_t t)")
    p.fix("t")
    p.assume("ih: is_term t")
    at_succ_t = SPEC(p._parse("t"), IS_TERM_AT_SUCC)
    p.thus("is_term (Succ_t t)").by_eq_mp(SYM(at_succ_t), "ih")


@proof
def IS_TERM_NUMERAL(p):
    """|- !n. is_term (numeral n)."""
    p.goal("!n. is_term (numeral n)")
    p.fix("n")
    with p.induction("n"):
        with p.base():
            p.have("eq0: numeral 0 = Zero_t").by_thm(NUMERAL_BASE)
            p.thus("is_term (numeral 0)").by_rewrite_of(IS_TERM_ZERO, [SYM(p.fact("eq0"))])
        with p.step("IH"):
            p.have("eq_step: numeral (SUC0 n) = Succ_t (numeral n)").by(
                NUMERAL_STEP, "n"
            )
            p.have("succ_term: is_term (Succ_t (numeral n))").by(
                IS_TERM_SUCC, "numeral n", "IH"
            )
            p.thus("is_term (numeral (SUC0 n))").by_rewrite_of(
                "succ_term", [SYM(p.fact("eq_step"))]
            )


# ---------------------------------------------------------------------------
# Stage 3A (c) -- representability scaffolding.
#
# A unary predicate ``P : nat0 -> bool`` is *represented* by a
# Q-formula ``F`` (a nat0 godelnum, taken to be a Q-formula whose only
# free variable is ``var_x``) iff:
#
#   * (positive)  !n. P n      ==> Prov_Q (substitute F (numeral n) var_x).
#   * (negative)  !n. ~ P n    ==> Prov_Q (Not_f (substitute F (numeral n) var_x)).
#
# We package the conjunction of the two conditions as
# ``represents_pred F P``.
#
# ``represents_func`` and the various function-arity variants are
# deferred to Stage 3B/C.
# ---------------------------------------------------------------------------


substitute = mk_const("substitute", [])
Not_f = mk_const("Not_f", [])


_F_n0 = Var("F", nat0_ty)
_P_pred = Var("P", parse_type("nat0 -> bool"))


def _subst_at_numeral(F_term, n_term):
    """Build ``substitute F (numeral n) var_x``."""
    return mk_app(substitute, F_term, mk_app(numeral, n_term), var_x)


_pos_clause = mk_forall(_n_n0,
    mk_imp(mk_app(_P_pred, _n_n0),
           mk_app(Prov_Q, _subst_at_numeral(_F_n0, _n_n0))))
_neg_clause = mk_forall(_n_n0,
    mk_imp(mk_not(mk_app(_P_pred, _n_n0)),
           mk_app(Prov_Q,
                  mk_app(Not_f, _subst_at_numeral(_F_n0, _n_n0)))))

_represents_pred_body = mk_and(_pos_clause, _neg_clause)

REPRESENTS_PRED_DEF = define(
    "represents_pred",
    parse_type("nat0 -> (nat0 -> bool) -> bool"),
    mk_abs(_F_n0, mk_abs(_P_pred, _represents_pred_body)),
)
represents_pred = mk_const("represents_pred", [])


def _at1(def_th, x):
    th = AP_THM(def_th, x)
    th = TRANS(th, BETA_CONV(rand(th._concl)))
    return GEN(x, th)


def _at2(def_th, x, y):
    th_x = AP_THM(def_th, x)
    th_x = TRANS(th_x, BETA_CONV(rand(th_x._concl)))
    th_xy = AP_THM(th_x, y)
    th_xy = TRANS(th_xy, BETA_CONV(rand(th_xy._concl)))
    return GENL([x, y], th_xy)


# |- !F P. represents_pred F P =
#          ((!n. P n ==> Prov_Q (substitute F (numeral n) var_x))
#        /\ (!n. ~ P n
#               ==> Prov_Q (Not_f (substitute F (numeral n) var_x)))).
REPRESENTS_PRED_AT = _at2(REPRESENTS_PRED_DEF, _F_n0, _P_pred)


# ---------------------------------------------------------------------------
# Stage 3B (a) -- list membership ``mem_l``.
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
    return mk_exists(_h_n0_local, mk_exists(_t_n0_local, mk_and(
        mk_eq(p_t, mk_app(cons_l, _h_n0_local, _t_n0_local)),
        mk_or(mk_eq(x_t, _h_n0_local),
              mk_app(f_t, _t_n0_local, x_t)),
    )))


_MEM_L_F_DEF = define(
    "_mem_l_F",
    _F_pred2_ty,
    mk_abs(_f_pred2, mk_abs(_p_n0_var,
        mk_abs(_x_n0_for_mem,
               _mem_l_body(_f_pred2, _p_n0_var, _x_n0_for_mem)))),
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
        "!f g p. (!k. nat0_lt k p ==> f k = g k) ==> "
        "_mem_l_F f p = _mem_l_F g p",
        types={"f": _pred2_ty, "g": _pred2_ty,
               "p": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g p")
    p.assume("h: !k. nat0_lt k p ==> f k = g k")

    h_th = p.fact("h")
    body_eq = mono_iff_eq_or_pw_step(
        cons_l, NAT0_LT_CONS_L_TAIL, h_th, _x_n0_for_mem
    )
    # body_eq : {h_concl} |- body[f, p, x] = body[g, p, x].
    abs_eq = ABS(_x_n0_for_mem, body_eq)
    # abs_eq : {h_concl} |- (\x. body[f, p, x]) = (\x. body[g, p, x]).

    p.thus(
        "_mem_l_F f p = _mem_l_F g p"
    ).by_unfold(abs_eq, _MEM_L_F_DEF)


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
    spec_p = SPEC(_p_n0_var, MEM_L_REC)         # |- mem_l p = \x. body
    ap_x = AP_THM(spec_p, _x_n0_for_mem)         # |- mem_l p x = (\x. body) x
    rhs = rand(ap_x._concl)
    beta_x = BETA_CONV(rhs)                      # |- (\x. body) x = body[x]
    pw = TRANS(ap_x, beta_x)                     # |- mem_l p x = body[x]
    return GENL([_p_n0_var, _x_n0_for_mem], pw)


MEM_L_REC_PW = _mem_l_rec_pw()


# Constructor equations: nil_l and cons_l.
#
#   |- !x. mem_l nil_l x = F.
#   |- !h t x. mem_l (cons_l h t) x =
#              (x = h \/ mem_l t x).


_MEM_L_RHS_STR = (
    "?h t. nil_l = cons_l h t /\\ (x = h \\/ mem_l t x)"
)


@proof
def MEM_L_AT_NIL(p):
    """|- !x. mem_l nil_l x = F."""
    p.goal("!x. mem_l nil_l x = F")
    p.fix("x")

    rec_at_nil_x = SPECL(
        [p._parse("nil_l"), p._parse("x")], MEM_L_REC_PW
    )
    # rec_at_nil_x : |- mem_l nil_l x =
    #                  (?h t. nil_l = cons_l h t /\ (x = h \/ mem_l t x))

    # Show RHS = F via ~RHS:
    with p.have(f"rhs_neg: ~({_MEM_L_RHS_STR})").proof():
        with p.suppose(f"hex: {_MEM_L_RHS_STR}"):
            p.choose("h", "hex", eq_label="ex_t")
            p.choose("t", "ex_t", eq_label="conj_ht")
            p.split("conj_ht", "(eq_nil, _disj)")
            p.have(
                "eq_swap: cons_l h t = nil_l"
            ).by_thm(SYM(p.fact("eq_nil")))
            p.have("neq: ~(cons_l h t = nil_l)").by(CONS_L_NEQ_NIL, "h", "t")
            p.absurd().by_conj("neq", "eq_swap")

    p.have(f"rhs_F: ({_MEM_L_RHS_STR}) = F").by_thm(
        EQF_INTRO(p.fact("rhs_neg"))
    )
    p.thus("mem_l nil_l x = F").by_thm(
        TRANS(rec_at_nil_x, p.fact("rhs_F"))
    )


@proof
def MEM_L_AT_CONS(p):
    """|- !h t x. mem_l (cons_l h t) x = (x = h \\/ mem_l t x)."""
    p.goal("!h t x. mem_l (cons_l h t) x = (x = h \\/ mem_l t x)")
    p.fix("h t x")

    rec_at = SPECL(
        [p._parse("cons_l h t"), p._parse("x")], MEM_L_REC_PW
    )
    # rec_at : |- mem_l (cons_l h t) x =
    #            (?h1 t1. cons_l h t = cons_l h1 t1
    #                     /\ (x = h1 \/ mem_l t1 x))

    rhs_str = (
        "?h1 t1. cons_l h t = cons_l h1 t1 /\\ "
        "(x = h1 \\/ mem_l t1 x)"
    )
    target_str = "x = h \\/ mem_l t x"

    # Forward: RHS ==> target.
    with p.have(f"fwd: ({rhs_str}) ==> ({target_str})").proof():
        p.assume(f"hex: {rhs_str}")
        p.choose("h1", "hex", eq_label="ex_t")
        p.choose("t1", "ex_t", eq_label="conj")
        p.split("conj", "(eq_cons, disj)")
        p.have("inj: h = h1 /\\ t = t1").by(
            CONS_L_INJ, "h", "t", "h1", "t1", "eq_cons"
        )
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
        outer_pred = mk_abs(h1_var,
            mk_exists(t1_var, outer_inner_body))
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
        mk_exists(_f1_n0_vs, mk_exists(_f2_n0_vs, mk_and(
            mk_app(mem_l, _t_n0_vs, _f1_n0_vs),
            mk_and(
                mk_app(mem_l, _t_n0_vs, _f2_n0_vs),
                mk_app(is_mp, _f1_n0_vs, _f2_n0_vs, _h_n0_vs),
            ),
        ))),
        mk_exists(_f1_n0_vs, mk_and(
            mk_app(mem_l, _t_n0_vs, _f1_n0_vs),
            mk_app(is_gen, _f1_n0_vs, _h_n0_vs),
        )),
    ),
)


VALID_STEP_DEF = define(
    "valid_step",
    parse_type("nat0 -> nat0 -> bool"),
    mk_abs(_t_n0_vs, mk_abs(_h_n0_vs, _valid_step_body)),
)
valid_step = mk_const("valid_step", [])


# Pointwise:
#   |- !t h. valid_step t h =
#            (is_axiom h
#             \/ (?f1 f2. mem_l t f1 /\ mem_l t f2 /\ is_mp f1 f2 h)
#             \/ (?f1. mem_l t f1 /\ is_gen f1 h)).
VALID_STEP_AT = _at2(VALID_STEP_DEF, _t_n0_vs, _h_n0_vs)


# ---------------------------------------------------------------------------
# Stage 3B (c) -- list-based provability ``Proof_Q``.
#
#   Proof_Q p n  :<=>
#       ?h t. p = cons_l h t /\ h = n /\ valid_step t h /\
#             (t = nil_l \/ ?h_inner. Proof_Q t h_inner).
#
# A non-empty list ``p`` whose head ``h`` equals ``n``, every prefix is
# justified by ``valid_step`` against its tail, and (via the inner
# disjunction) the tail itself extends to a valid proof or is empty.
# When ``p = nil_l`` the body is F (no h, t with nil_l = cons_l h t,
# CONS_L_NEQ_NIL).
#
# Recursion target type is ``nat0 -> bool`` (Proof_Q : nat0 -> nat0 ->
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
    return mk_exists(_h_n0_pq, mk_exists(_t_n0_pq, mk_and(
        mk_eq(p_t, mk_app(cons_l, _h_n0_pq, _t_n0_pq)),
        mk_and(
            mk_eq(_h_n0_pq, n_t),
            mk_and(
                mk_app(valid_step, _t_n0_pq, _h_n0_pq),
                mk_or(
                    mk_eq(_t_n0_pq, nil_l),
                    mk_exists(_h_inner_pq,
                              mk_app(f_t, _t_n0_pq, _h_inner_pq)),
                ),
            ),
        ),
    )))


_PROOF_Q_F_DEF = define(
    "_proof_q_F",
    _F_pred2_ty,
    mk_abs(_f_pred2, mk_abs(_p_n0_var,
        mk_abs(_n_n0_pq,
               _proof_q_body(_f_pred2, _p_n0_var, _n_n0_pq)))),
)
_PROOF_Q_F = mk_const("_proof_q_F", [])


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
                        mk_exists(_h_inner_pq,
                                  mk_app(fn, _t_n0_pq, _h_inner_pq)),
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

        new_body = CONJ(n_eq_th,
            CONJ(h_eq_n_th, CONJ(valid_th, new_disj_th)))

        inner_pred_at_wh = mk_abs(
            _t_n0_pq, vsubst([(wh, _h_n0_pq)])(target_inner_body))
        inner_th = EXISTS(inner_pred_at_wh, wt, new_body)
        outer_pred_body = mk_abs(
            _h_n0_pq, mk_exists(_t_n0_pq, target_inner_body))
        outer_th = EXISTS(outer_pred_body, wh, inner_th)
        return outer_th

    R_th = _direction(LHS, body_inner_r, swap_fg=False)
    L_th = _direction(RHS, body_inner_l, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


@proof
def PROOF_Q_MONO(p):
    """|- !f g p. (!k. nat0_lt k p ==> f k = g k)
                  ==> _proof_q_F f p = _proof_q_F g p."""
    p.goal(
        "!f g p. (!k. nat0_lt k p ==> f k = g k) ==> "
        "_proof_q_F f p = _proof_q_F g p",
        types={"f": _pred2_ty, "g": _pred2_ty,
               "p": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g p")
    p.assume("hyp: !k. nat0_lt k p ==> f k = g k")

    body_eq = _proof_q_mono_body_iff(p.fact("hyp"), _n_n0_pq)
    abs_eq = ABS(_n_n0_pq, body_eq)
    p.thus(
        "_proof_q_F f p = _proof_q_F g p"
    ).by_unfold(abs_eq, _PROOF_Q_F_DEF)


PROOF_Q_DEF, _PROOF_Q_REC_RAW = define_wf_lt(
    "Proof_Q",
    _pred2_ty,
    _PROOF_Q_F,
    PROOF_Q_MONO,
)
Proof_Q = mk_const("Proof_Q", [])


# |- !p. Proof_Q p =
#         (\n. ?h t. p = cons_l h t /\ h = n /\ valid_step t h
#                    /\ (t = nil_l \/ ?h_inner. Proof_Q t h_inner)).
PROOF_Q_REC = _unfold_rec_via_F_def(_PROOF_Q_REC_RAW, _PROOF_Q_F_DEF)


# Pointwise unfold:
#   |- !p n. Proof_Q p n =
#            (?h t. p = cons_l h t /\ h = n /\ valid_step t h
#                   /\ (t = nil_l \/ ?h_inner. Proof_Q t h_inner)).
def _proof_q_rec_pw():
    spec_p = SPEC(_p_n0_var, PROOF_Q_REC)
    ap_n = AP_THM(spec_p, _n_n0_pq)
    rhs = rand(ap_n._concl)
    beta_n = BETA_CONV(rhs)
    pw = TRANS(ap_n, beta_n)
    return GENL([_p_n0_var, _n_n0_pq], pw)


PROOF_Q_REC_PW = _proof_q_rec_pw()


# Constructor equations.
_PROOF_Q_RHS_NIL_STR = (
    "?h t. nil_l = cons_l h t /\\ h = n /\\ valid_step t h /\\ "
    "(t = nil_l \\/ ?h_inner. Proof_Q t h_inner)"
)


@proof
def PROOF_Q_AT_NIL(p):
    """|- !n. Proof_Q nil_l n = F."""
    p.goal("!n. Proof_Q nil_l n = F")
    p.fix("n")

    rec_at = SPECL([p._parse("nil_l"), p._parse("n")], PROOF_Q_REC_PW)

    with p.have(f"rhs_neg: ~({_PROOF_Q_RHS_NIL_STR})").proof():
        with p.suppose(f"hex: {_PROOF_Q_RHS_NIL_STR}"):
            p.choose("h", "hex", eq_label="ex_t")
            p.choose("t", "ex_t", eq_label="conj_ht")
            p.split("conj_ht", "(eq_nil, _rest)")
            p.have(
                "eq_swap: cons_l h t = nil_l"
            ).by_thm(SYM(p.fact("eq_nil")))
            p.have("neq: ~(cons_l h t = nil_l)").by(CONS_L_NEQ_NIL, "h", "t")
            p.absurd().by_conj("neq", "eq_swap")

    p.have(f"rhs_F: ({_PROOF_Q_RHS_NIL_STR}) = F").by_thm(
        EQF_INTRO(p.fact("rhs_neg"))
    )
    p.thus("Proof_Q nil_l n = F").by_thm(
        TRANS(rec_at, p.fact("rhs_F"))
    )


@proof
def PROOF_Q_AT_CONS(p):
    """|- !h t n. Proof_Q (cons_l h t) n =
                  (h = n /\\ valid_step t h
                   /\\ (t = nil_l \\/ ?h_inner. Proof_Q t h_inner))."""
    p.goal(
        "!h t n. Proof_Q (cons_l h t) n = "
        "(h = n /\\ valid_step t h "
        "/\\ (t = nil_l \\/ ?h_inner. Proof_Q t h_inner))"
    )
    p.fix("h t n")

    rec_at = SPECL(
        [p._parse("cons_l h t"), p._parse("n")], PROOF_Q_REC_PW
    )
    rhs_str = (
        "?h1 t1. cons_l h t = cons_l h1 t1 /\\ h1 = n /\\ "
        "valid_step t1 h1 /\\ "
        "(t1 = nil_l \\/ ?h_inner. Proof_Q t1 h_inner)"
    )
    target_str = (
        "h = n /\\ valid_step t h /\\ "
        "(t = nil_l \\/ ?h_inner. Proof_Q t h_inner)"
    )

    # Forward: RHS ==> target.
    #
    # The disjunction inner-existential (?h_inner. Proof_Q t1 h_inner)
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
        p.have("inj: h = h1 /\\ t = t1").by(
            CONS_L_INJ, "h", "t", "h1", "t1", "eq_cons"
        )
        p.split("inj", "(eq_h, eq_t)")
        p.have("h_eq_n: h = n").by_rewrite_of(
            "h1_eq_n", [SYM(p.fact("eq_h"))]
        )
        p.have("valid_th: valid_step t h").by_rewrite_of(
            "valid_t1", [SYM(p.fact("eq_h")), SYM(p.fact("eq_t"))]
        )
        with p.have(
            "disj_th: t = nil_l \\/ ?h_inner. Proof_Q t h_inner"
        ).proof():
            with p.cases_on("disj_t1"):
                with p.case("nil_c: t1 = nil_l"):
                    p.have("t_eq_nil: t = nil_l").by_rewrite_of(
                        "nil_c", [SYM(p.fact("eq_t"))]
                    )
                    p.thus(
                        "t = nil_l \\/ ?h_inner. Proof_Q t h_inner"
                    ).by_disj("t_eq_nil")
                with p.case("ex_c: ?h_inner. Proof_Q t1 h_inner"):
                    # case auto-introduces ``h_inner`` witness with eq
                    # fact ``h_inner_eq: Proof_Q t1 h_inner``.
                    p.have("pq_at_t: Proof_Q t h_inner").by_rewrite_of(
                        "h_inner_eq", [SYM(p.fact("eq_t"))]
                    )
                    # Build the existential and disj manually (the
                    # ``disj_witness`` machinery here mismatches because
                    # ``h_inner`` resolves through the case's choose_env
                    # to a SELECT term whose body REWRITE_PROVE struggles
                    # to align).
                    h_inner_term = p._parse("h_inner")
                    t_term = p._parse("t")
                    inner_pred = mk_abs(
                        _h_inner_pq, mk_app(Proof_Q, t_term, _h_inner_pq))
                    exists_th = EXISTS(inner_pred, h_inner_term, p.fact("pq_at_t"))
                    p.thus(
                        "t = nil_l \\/ ?h_inner. Proof_Q t h_inner"
                    ).by_thm(DISJ2(p._parse("t = nil_l"), exists_th))
        p.thus(target_str).by_thm(
            CONJ(p.fact("h_eq_n"),
                 CONJ(p.fact("valid_th"), p.fact("disj_th")))
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

        body_th = CONJ(REFL(cons_h_t),
            CONJ(p.fact("h_eq_n"),
                CONJ(p.fact("valid_th"), p.fact("disj_th"))))

        inner_body_t1 = mk_and(
            mk_eq(cons_h_t, mk_app(cons_l, h_t, t1_var)),
            mk_and(
                mk_eq(h_t, n_t),
                mk_and(
                    mk_app(valid_step, t1_var, h_t),
                    mk_or(
                        mk_eq(t1_var, nil_l),
                        mk_exists(_h_inner_pq,
                                  mk_app(Proof_Q, t1_var, _h_inner_pq)),
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
                        mk_exists(_h_inner_pq,
                                  mk_app(Proof_Q, t1_var, _h_inner_pq)),
                    ),
                ),
            ),
        )
        outer_pred = mk_abs(h1_var,
            mk_exists(t1_var, outer_inner_body))
        outer_th = EXISTS(outer_pred, h_t, inner_th)
        p.thus(rhs_str).by_thm(outer_th)

    p.have(f"iff: ({rhs_str}) = ({target_str})").by_iff("fwd", "rev")
    p.thus(
        "Proof_Q (cons_l h t) n = "
        "(h = n /\\ valid_step t h "
        "/\\ (t = nil_l \\/ ?h_inner. Proof_Q t h_inner))"
    ).by_thm(TRANS(rec_at, p.fact("iff")))


# ---------------------------------------------------------------------------
# Roadmap -- Stage 3B and 3C.
# ---------------------------------------------------------------------------
#
# Stage 3B (proof witnesses inside HOL):
#
#   * Define ``mem_l`` (list membership) via ``define_wf_lt``         [DONE]
#     using ``NAT0_LT_CONS_L_TAIL`` from ``q_proof``. The MONO
#     obligation reuses ``mono_iff_eq_or_pw_step`` (q_syntax) at
#     ``cons_l`` to peel the existential under the cons-witness.
#     ``MEM_L_AT_NIL`` discharged via ``CONS_L_NEQ_NIL``;
#     ``MEM_L_AT_CONS`` via ``CONS_L_INJ``.
#
#   * Define ``valid_step``                                          [DONE]
#     non-recursive disjunction over is_axiom, an MP existential,
#     and a Gen existential (each consuming ``mem_l t _``).
#
#   * Define ``Proof_Q : nat0 -> nat0 -> bool`` via ``define_wf_lt``  [DONE]
#     with body
#       ?h t. p = cons_l h t /\ h = n /\ valid_step t h
#             /\ (t = nil_l \/ ?h'. Proof_Q t h').
#     ``PROOF_Q_AT_NIL`` discharges via ``CONS_L_NEQ_NIL``;
#     ``PROOF_Q_AT_CONS`` via ``CONS_L_INJ`` + cases-split on the
#     inner disjunction (the rewrite under the inner ``?h_inner``
#     binder doesn't fire on hyp-laden rules, so each disjunct case
#     handles its rewrite at the top level).
#
#   * Prove the equivalence with the impredicative ``Prov_Q``:
#         |- !n. Prov_Q n <=> ?p. Proof_Q p n.
#     Forward (?p ==> Prov_Q): induction on the proof list, using
#     PROV_Q_AXIOM / PROV_Q_MP / PROV_Q_GEN at each step.
#     Backward (Prov_Q ==> ?p): instantiate ``P := \n. ?p. Proof_Q p n``
#     in PROV_Q_AT and verify the three closure clauses by exhibiting
#     extended proof lists.
#
#   * Representability of ``substitute``: Sigma_1 formula
#     ``substitute_internal`` such that
#         |- !F t v. Prov_Q (substitute_internal_eq F t v
#                                                  (numeral
#                                                   (substitute F t v))).
#     Standard induction on F; ~200 lines with the recursion equations
#     from Stage 1.
#
# Stage 3C (representability of provability):
#
#   * Define ``Proof_Q_internal``: a Q-formula in two free variables
#     ``var_x``, ``var_y`` such that ``substitute_2 Proof_Q_internal
#     (numeral p) (numeral n) var_x var_y`` is Q-provable iff
#     ``Proof_Q p n`` holds. Constructed bottom-up from
#     ``substitute_internal``, ``is_axiom_internal``, ``is_mp_internal``,
#     ``is_gen_internal`` -- each itself a representable predicate.
#
#   * Define ``Prov_Q_internal n := ?_internal var_y. Proof_Q_internal``
#     where ``?_internal`` is encoded as ``~!y. ~``.
#
#   * Headline theorem:
#         |- !n. Prov_Q n <=>
#                 Prov_Q (godelnum (Prov_Q_internal (numeral n))).
#     Forward: Prov_Q n => ?p. Proof_Q p n => Q proves the Sigma_1
#     statement Proof_Q_internal(numeral p, numeral n) by Sigma_1
#     completeness => Q proves Prov_Q_internal(numeral n) by EXISTS.
#     Backward: Sigma_1 soundness (proved in Stage 6 from the HF model).


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 3A (a) -- numeral function.")
    print("    NUMERAL_BASE :", pp_thm(NUMERAL_BASE))
    print("    NUMERAL_STEP :", pp_thm(NUMERAL_STEP))
    print()
    print("Stage 3A (b) -- IS_TERM_NUMERAL.")
    print("    IS_TERM_ZERO     :", pp_thm(IS_TERM_ZERO))
    print("    IS_TERM_SUCC     :", pp_thm(IS_TERM_SUCC))
    print("    IS_TERM_NUMERAL  :", pp_thm(IS_TERM_NUMERAL))
    print()
    print("Stage 3A (c) -- representability scaffolding.")
    print("    REPRESENTS_PRED_DEF :", pp_thm(REPRESENTS_PRED_DEF))
    print("    REPRESENTS_PRED_AT  :", pp_thm(REPRESENTS_PRED_AT))
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
    print("Stage 3B (c) -- list-based Proof_Q.")
    print("    PROOF_Q_DEF      :", pp_thm(PROOF_Q_DEF))
    print("    PROOF_Q_REC      :", pp_thm(PROOF_Q_REC))
    print("    PROOF_Q_REC_PW   :", pp_thm(PROOF_Q_REC_PW))
    print("    PROOF_Q_AT_NIL   :", pp_thm(PROOF_Q_AT_NIL))
    print("    PROOF_Q_AT_CONS  :", pp_thm(PROOF_Q_AT_CONS))
