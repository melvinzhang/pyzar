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

from fusion import Var
from basics import mk_const, mk_app, mk_abs, rand, rator
from parser import define, parse_type
from axioms import mk_forall, mk_imp, mk_not, mk_and, mk_or, mk_exists
from nat0 import nat0_ty, define_unary_0
from nat0_order import define_wf_lt
from proof import proof
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

from q_syntax import (
    Zero_t,
    Succ_t,
    is_term_const,
    IS_TERM_REC,
    IS_TERM_AT_SUCC,
    mono_iff_eq_or_pw_step,
    _unfold_rec_via_F_def,
    _extract_nfg,
    _mono_iff_value_binary_pw_step,
)
from axioms import mk_select
from axioms import dest_exists
from tactics import (
    CHOOSE_WITNESS,
    AP_TERM,
    OR_CONG,
    REWRITE_RULE,
)
from fusion import vsubst, aty, DEDUCT_ANTISYM_RULE, new_constant
from q_proof import (
    var_x,
    nil_l,
    cons_l,
    CONS_L_INJ,
    CONS_L_NEQ_NIL,
    NAT0_LT_CONS_L_TAIL,
    is_axiom,
    is_mp,
    is_gen,
    IS_MP_AT,
    IS_GEN_AT,
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
    from basics import rand as _rand

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
            p.thus("is_term (numeral 0)").by_rewrite_of(
                IS_TERM_ZERO, [SYM(p.fact("eq0"))]
            )
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
# Stage 3A (c) -- shared constants and helpers used by the Stage 3B
# Proof_Q infrastructure and beyond.
#
# ``substitute`` and ``Not_f`` are referenced by name from this point on;
# the ``represents_pred`` scaffolding (which mentions ``Prov_Q``) lives
# in Stage 3B (k) below, after ``Prov_Q`` has been defined as the
# Sigma_1 form ``\n. ?p. Proof_Q p n``.
# ---------------------------------------------------------------------------


substitute = mk_const("substitute", [])
Not_f = mk_const("Not_f", [])


_F_n0 = Var("F", nat0_ty)
_P_pred = Var("P", parse_type("nat0 -> bool"))


def _subst_at_numeral(F_term, n_term):
    """Build ``substitute F (numeral n) var_x``."""
    return mk_app(substitute, F_term, mk_app(numeral, n_term), var_x)


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


_PROOF_Q_F_DEF = define(
    "_proof_q_F",
    _F_pred2_ty,
    mk_abs(
        _f_pred2,
        mk_abs(
            _p_n0_var, mk_abs(_n_n0_pq, _proof_q_body(_f_pred2, _p_n0_var, _n_n0_pq))
        ),
    ),
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
def PROOF_Q_MONO(p):
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
    p.thus("_proof_q_F f p = _proof_q_F g p").by_unfold(abs_eq, _PROOF_Q_F_DEF)


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
            p.have("eq_swap: cons_l h t = nil_l").by_thm(SYM(p.fact("eq_nil")))
            p.have("neq: ~(cons_l h t = nil_l)").by(CONS_L_NEQ_NIL, "h", "t")
            p.absurd().by_conj("neq", "eq_swap")

    p.have(f"rhs_F: ({_PROOF_Q_RHS_NIL_STR}) = F").by_thm(EQF_INTRO(p.fact("rhs_neg")))
    p.thus("Proof_Q nil_l n = F").by_thm(TRANS(rec_at, p.fact("rhs_F")))


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

    rec_at = SPECL([p._parse("cons_l h t"), p._parse("n")], PROOF_Q_REC_PW)
    rhs_str = (
        "?h1 t1. cons_l h t = cons_l h1 t1 /\\ h1 = n /\\ "
        "valid_step t1 h1 /\\ "
        "(t1 = nil_l \\/ ?h_inner. Proof_Q t1 h_inner)"
    )
    target_str = (
        "h = n /\\ valid_step t h /\\ (t = nil_l \\/ ?h_inner. Proof_Q t h_inner)"
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
        p.have("inj: h = h1 /\\ t = t1").by(CONS_L_INJ, "h", "t", "h1", "t1", "eq_cons")
        p.split("inj", "(eq_h, eq_t)")
        p.have("h_eq_n: h = n").by_rewrite_of("h1_eq_n", [SYM(p.fact("eq_h"))])
        p.have("valid_th: valid_step t h").by_rewrite_of(
            "valid_t1", [SYM(p.fact("eq_h")), SYM(p.fact("eq_t"))]
        )
        with p.have("disj_th: t = nil_l \\/ ?h_inner. Proof_Q t h_inner").proof():
            with p.cases_on("disj_t1"):
                with p.case("nil_c: t1 = nil_l"):
                    p.have("t_eq_nil: t = nil_l").by_rewrite_of(
                        "nil_c", [SYM(p.fact("eq_t"))]
                    )
                    p.thus("t = nil_l \\/ ?h_inner. Proof_Q t h_inner").by_disj(
                        "t_eq_nil"
                    )
                with p.case("ex_c: ?h_inner. Proof_Q t1 h_inner"):
                    # case auto-introduces ``h_inner`` witness with eq
                    # fact ``h_inner_eq: Proof_Q t1 h_inner``.
                    p.have("pq_at_t: Proof_Q t h_inner").by_rewrite_of(
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
                        mk_exists(_h_inner_pq, mk_app(Proof_Q, t1_var, _h_inner_pq)),
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
                        mk_exists(_h_inner_pq, mk_app(Proof_Q, t1_var, _h_inner_pq)),
                    ),
                ),
            ),
        )
        outer_pred = mk_abs(h1_var, mk_exists(t1_var, outer_inner_body))
        outer_th = EXISTS(outer_pred, h_t, inner_th)
        p.thus(rhs_str).by_thm(outer_th)

    p.have(f"iff: ({rhs_str}) = ({target_str})").by_iff("fwd", "rev")
    p.thus(
        "Proof_Q (cons_l h t) n = "
        "(h = n /\\ valid_step t h "
        "/\\ (t = nil_l \\/ ?h_inner. Proof_Q t h_inner))"
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
# ``q_syntax`` for the cons disjunct (only the tail recurses, so
# ``recurses_l=False``, with size lemma ``NAT0_LT_CONS_L_TAIL``); the
# nil disjunct is non-recursive and falls through ``REFL``.
#
# Used in Stage 3B (e) to combine two proof-list witnesses (one ending
# at ``f``, one ending at ``Imp_f f g``) into a single longer list that
# witnesses ``Proof_Q``-derivability of ``g``: the ``Prov_Q ==> ?p.
# Proof_Q p n`` direction needs to verify the MP closure clause, which
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

    from q_syntax import _select_collapse_eq

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

    from q_syntax import _select_collapse_eq

    target_K = mk_app(cons_l, h_t, mk_app(append_l, t_t, q_t))
    collapse = _select_collapse_eq(target_K, _r_n0_app)
    full_eq = TRANS(body_at, TRANS(sel_eq, collapse))
    p.thus("append_l (cons_l h t) q = cons_l h (append_l t q)").by_thm(full_eq)


# ---------------------------------------------------------------------------
# Stage 3B (e) -- membership preservation under append.
#
#   |- !p1 h1. Proof_Q p1 h1 ==>
#       !p2 f. (mem_l p1 f \/ mem_l p2 f) ==> mem_l (append_l p1 p2) f.
#
# In words: if ``p1`` is a Q-proof (so it has the cons-of-nil-terminated
# shape recursively) then every element of ``p1`` and of ``p2`` is an
# element of the concatenation. Strong induction on ``p1``: PROOF_Q_AT
# unpacks ``p1 = cons_l hd tl``; the recursion either bottoms out at
# ``tl = nil_l`` (where ``append_l nil_l p2 = p2`` directly) or proceeds
# with ``Proof_Q tl h_inner`` (where the IH applies at ``tl`` and the
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
    """|- !p1 h1. Proof_Q p1 h1 ==>
    !p2 f. (mem_l p1 f \\/ mem_l p2 f)
           ==> mem_l (append_l p1 p2) f."""
    p.goal(
        "!p1. !h1. Proof_Q p1 h1 ==> "
        "!p2 f. (mem_l p1 f \\/ mem_l p2 f) "
        "==> mem_l (append_l p1 p2) f"
    )
    with p.strong_induction("p1", "IH"):
        p.fix("h1")
        p.assume("pq: Proof_Q p1 h1")
        p.fix("p2 f")
        p.assume("hd: mem_l p1 f \\/ mem_l p2 f")

        # Unfold pq to extract p1 = cons_l hd_v tl, hd_v = h1, etc.
        rec_pq = SPECL([p._parse("p1"), p._parse("h1")], PROOF_Q_REC_PW)
        body_str = (
            "?h t. p1 = cons_l h t /\\ h = h1 /\\ valid_step t h "
            "/\\ (t = nil_l \\/ ?h_inner. Proof_Q t h_inner)"
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
                        # tl is nil or has Proof_Q; in nil case mem_l = F.
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
                            with p.case("tex: ?h_inner. Proof_Q tl h_inner"):
                                # h_inner_eq: Proof_Q tl h_inner.
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
                    with p.case("tex: ?h_inner. Proof_Q tl h_inner"):
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
            p.choose("f2", "f1_eq", eq_label="conj_mp")
            p.split("conj_mp", "(mem_q1_f1, mem_q1_f2, mp_th)")
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
# Stage 3B (g) -- ``Proof_Q`` is preserved under list concatenation.
#
#   |- !p1 h1. Proof_Q p1 h1 ==>
#       !p2 h2. Proof_Q p2 h2 ==> Proof_Q (append_l p1 p2) h1.
#
# Strong induction on ``p1``. Unpack ``Proof_Q p1 h1`` to
# ``p1 = cons_l hd tl`` and case-split on the inner tail disjunct:
#
#   * ``tl = nil_l``: ``append_l p1 p2 = cons_l hd p2``. The membership
#     premise is vacuous (``mem_l nil_l _ = F``) so ``valid_step nil_l hd
#     ==> valid_step p2 hd`` discharges trivially via
#     ``VALID_STEP_PRESERVES``. Tail-of-tail disjunct uses ``Proof_Q p2 h2``.
#
#   * ``Proof_Q tl h_inner``: IH at ``tl`` gives
#     ``Proof_Q (append_l tl p2) h_inner``; ``MEM_L_APPEND_PRESERVES`` (with
#     ``mem_l tl f \\/ mem_l p2 f`` ⇒ ``mem_l (append_l tl p2) f``) lifts
#     ``valid_step tl hd`` into ``valid_step (append_l tl p2) hd``.
# ---------------------------------------------------------------------------


@proof
def PROOF_Q_APPEND(p):
    """|- !p1 h1 p2 h2. Proof_Q p1 h1 ==> Proof_Q p2 h2
    ==> Proof_Q (append_l p1 p2) h1."""
    p.goal(
        "!p1. !h1. Proof_Q p1 h1 ==> "
        "!p2 h2. Proof_Q p2 h2 "
        "==> Proof_Q (append_l p1 p2) h1"
    )
    with p.strong_induction("p1", "IH"):
        p.fix("h1")
        p.assume("pq1: Proof_Q p1 h1")
        p.fix("p2 h2")
        p.assume("pq2: Proof_Q p2 h2")

        rec_pq1 = SPECL([p._parse("p1"), p._parse("h1")], PROOF_Q_REC_PW)
        body_str = (
            "?h t. p1 = cons_l h t /\\ h = h1 /\\ valid_step t h "
            "/\\ (t = nil_l \\/ ?h_inner. Proof_Q t h_inner)"
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
            PROOF_Q_AT_CONS,
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

                # Proof_Q p2 h2 lifts to Proof_Q (append_l tl p2) h2.
                pq_eq = AP_THM(
                    AP_TERM(Proof_Q, p.fact("app_tl_eq_p2")),
                    p._parse("h2"),
                )
                p.have("pq_app: Proof_Q (append_l tl p2) h2").by_eq_mp(pq_eq, "pq2")
                p.have("ex_app: ?h_inner. Proof_Q (append_l tl p2) h_inner").by_witness(
                    "h2", "pq_app"
                )
                p.have(
                    "tail_app_disj: "
                    "(append_l tl p2) = nil_l "
                    "\\/ ?h_inner. Proof_Q (append_l tl p2) h_inner"
                ).by_disj("ex_app")

                p.have(
                    "target_body: hd = h1 /\\ "
                    "valid_step (append_l tl p2) hd /\\ "
                    "((append_l tl p2) = nil_l "
                    "\\/ ?h_inner. Proof_Q (append_l tl p2) h_inner)"
                ).by_thm(
                    CONJ(
                        p.fact("hd_eq_h1"),
                        CONJ(p.fact("valid_app"), p.fact("tail_app_disj")),
                    )
                )
                p.have("pq_cons: Proof_Q (cons_l hd (append_l tl p2)) h1").by_eq_mp(
                    SYM(target_eq), "target_body"
                )
                p.thus("Proof_Q (append_l p1 p2) h1").by_rewrite_of(
                    "pq_cons", [SYM(p.fact("app_eq"))]
                )

            with p.case("tex: ?h_inner. Proof_Q tl h_inner"):
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

                p.have("pq_app: Proof_Q (append_l tl p2) h_inner").by(
                    "IH", "tl", "lt_tl_p1", "h_inner", "h_inner_eq", "p2", "h2", "pq2"
                )

                p.have("ex_app: ?h_inner. Proof_Q (append_l tl p2) h_inner").by_witness(
                    "h_inner", "pq_app"
                )
                p.have(
                    "tail_app_disj: "
                    "(append_l tl p2) = nil_l "
                    "\\/ ?h_inner. Proof_Q (append_l tl p2) h_inner"
                ).by_disj("ex_app")

                p.have(
                    "target_body: hd = h1 /\\ "
                    "valid_step (append_l tl p2) hd /\\ "
                    "((append_l tl p2) = nil_l "
                    "\\/ ?h_inner. Proof_Q (append_l tl p2) h_inner)"
                ).by_thm(
                    CONJ(
                        p.fact("hd_eq_h1"),
                        CONJ(p.fact("valid_app"), p.fact("tail_app_disj")),
                    )
                )
                p.have("pq_cons: Proof_Q (cons_l hd (append_l tl p2)) h1").by_eq_mp(
                    SYM(target_eq), "target_body"
                )
                p.thus("Proof_Q (append_l p1 p2) h1").by_rewrite_of(
                    "pq_cons", [SYM(p.fact("app_eq"))]
                )


# ---------------------------------------------------------------------------
# (DELETED) Forward direction of an old Prov_Q / Proof_Q equivalence.
#
# An earlier draft proved
#   |- !p f. mem_l p f ==> (?h. Proof_Q p h) ==> Prov_Q f
# by strong induction on the proof list, then derived the convenience
# corollary ``PROOF_Q_PROVES : !p n. Proof_Q p n ==> Prov_Q n``. Both
# were needed only because ``Prov_Q`` was originally defined
# impredicatively in q_proof.py and had to be bridged to the list-based
# ``Proof_Q``. After collapsing ``Prov_Q := \n. ?p. Proof_Q p n``
# (defined later in this file via the Sigma_1 form), ``PROOF_Q_PROVES``
# becomes ``EXISTS_INTRO`` and the strong-induction argument is no
# longer needed for any downstream consumer. Both lemmas are retired.
# ---------------------------------------------------------------------------



# ---------------------------------------------------------------------------
# Stage 3B (h) -- ``Proof_Q p h ==> mem_l p h`` (head is its own member).
# ---------------------------------------------------------------------------


@proof
def PROOF_Q_HEAD_MEM(p):
    """|- !p1 h1. Proof_Q p1 h1 ==> mem_l p1 h1."""
    p.goal("!p1 h1. Proof_Q p1 h1 ==> mem_l p1 h1")
    p.fix("p1 h1")
    p.assume("pq: Proof_Q p1 h1")
    rec_pq = SPECL([p._parse("p1"), p._parse("h1")], PROOF_Q_REC_PW)
    body_str = (
        "?h t. p1 = cons_l h t /\\ h = h1 /\\ valid_step t h "
        "/\\ (t = nil_l \\/ ?h_inner. Proof_Q t h_inner)"
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
# Stage 3B (i) -- the three admissibility clauses for the
# impredicative ``Prov_Q``, lifted to ``\n. ?p. Proof_Q p n``.
# ---------------------------------------------------------------------------


@proof
def AXIOM_HAS_PROOF(p):
    """|- !m. is_axiom m ==> ?p. Proof_Q p m.

    Witness: ``cons_l m nil_l``. Validity: ``valid_step nil_l m``
    follows directly from ``is_axiom m`` via the axiom disjunct;
    tail disjunct collapses to ``nil_l = nil_l``.
    """
    p.goal("!m. is_axiom m ==> ?p. Proof_Q p m")
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
    p.have("tail_disj: nil_l = nil_l \\/ ?h_inner. Proof_Q nil_l h_inner").by_disj(
        REFL(nil_l)
    )

    target_eq = SPECL(
        [p._parse("m"), nil_l, p._parse("m")],
        PROOF_Q_AT_CONS,
    )
    p.have(
        "target_body: m = m /\\ valid_step nil_l m "
        "/\\ (nil_l = nil_l "
        "\\/ ?h_inner. Proof_Q nil_l h_inner)"
    ).by_thm(
        CONJ(
            REFL(p._parse("m")),
            CONJ(p.fact("valid_th"), p.fact("tail_disj")),
        )
    )
    p.have("pq_witness: Proof_Q (cons_l m nil_l) m").by_eq_mp(
        SYM(target_eq), "target_body"
    )
    p.thus("?p. Proof_Q p m").by_witness("cons_l m nil_l", "pq_witness")


@proof
def GEN_HAS_PROOF(p):
    """|- !f x. (?p1. Proof_Q p1 f) ==>
                ?p. Proof_Q p (Forall_f x f).

    Witness: ``cons_l (Forall_f x f) p1``. Validity: Gen disjunct of
    ``valid_step p1 (Forall_f x f)`` with member ``f`` (head of ``p1``)
    and ``is_gen f (Forall_f x f)`` (witness ``x`` for the inner
    existential). Tail disjunct: right with witness ``f`` (since
    ``Proof_Q p1 f``).
    """
    p.goal("!f x. (?p1. Proof_Q p1 f) ==> ?p. Proof_Q p (Forall_f x f)")
    p.fix("f x")
    p.assume("pq_ex: ?p1. Proof_Q p1 f")
    p.choose("p1", "pq_ex", eq_label="pq1")

    p.have("mem_p1_f: mem_l p1 f").by(PROOF_Q_HEAD_MEM, "p1", "f", "pq1")

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

    # Tail disjunct: ?h_inner. Proof_Q p1 h_inner with witness f.
    p.have("tail_ex: ?h_inner. Proof_Q p1 h_inner").by_witness("f", "pq1")
    p.have("tail_disj: p1 = nil_l \\/ ?h_inner. Proof_Q p1 h_inner").by_disj("tail_ex")

    fa_t = p._parse("Forall_f x f")
    target_eq = SPECL(
        [fa_t, p._parse("p1"), fa_t],
        PROOF_Q_AT_CONS,
    )
    p.have(
        "target_body: Forall_f x f = Forall_f x f "
        "/\\ valid_step p1 (Forall_f x f) "
        "/\\ (p1 = nil_l "
        "\\/ ?h_inner. Proof_Q p1 h_inner)"
    ).by_thm(
        CONJ(
            REFL(fa_t),
            CONJ(p.fact("valid_th"), p.fact("tail_disj")),
        )
    )
    p.have("pq_witness: Proof_Q (cons_l (Forall_f x f) p1) (Forall_f x f)").by_eq_mp(
        SYM(target_eq), "target_body"
    )
    p.thus("?p. Proof_Q p (Forall_f x f)").by_witness(
        "cons_l (Forall_f x f) p1", "pq_witness"
    )


@proof
def MP_HAS_PROOF(p):
    """|- !f g. (?p1. Proof_Q p1 f) /\\ (?p2. Proof_Q p2 (Imp_f f g))
                 ==> ?p. Proof_Q p g.

    Witness: ``cons_l g (append_l p2 p1)``. Validity: MP disjunct
    with ``f1 := f``, ``f2 := Imp_f f g`` -- both members of
    ``append_l p2 p1`` via ``MEM_L_APPEND_PRESERVES`` (lifting
    ``mem_l p2 (Imp_f f g)`` and ``mem_l p1 f``). Tail disjunct:
    ``Proof_Q (append_l p2 p1) (Imp_f f g)`` from ``PROOF_Q_APPEND``.
    """
    p.goal(
        "!f g. (?p1. Proof_Q p1 f) /\\ "
        "(?p2. Proof_Q p2 (Imp_f f g)) "
        "==> ?p. Proof_Q p g"
    )
    p.fix("f g")
    p.assume("(pq1_ex, pq2_ex): (?p1. Proof_Q p1 f) /\\ (?p2. Proof_Q p2 (Imp_f f g))")
    p.choose("p1", "pq1_ex", eq_label="pq1")
    p.choose("p2", "pq2_ex", eq_label="pq2")

    # Members.
    p.have("mem_p1_f: mem_l p1 f").by(PROOF_Q_HEAD_MEM, "p1", "f", "pq1")
    p.have("mem_p2_imp: mem_l p2 (Imp_f f g)").by(
        PROOF_Q_HEAD_MEM, "p2", "Imp_f f g", "pq2"
    )

    # Lift via MEM_L_APPEND_PRESERVES with (p1' := p2, p2' := p1):
    #   Proof_Q p2 (Imp_f f g) ==> (mem_l p2 a \/ mem_l p1 a) ==>
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

    # Tail disjunction: ?h_inner. Proof_Q (append_l p2 p1) h_inner via
    # PROOF_Q_APPEND with witness Imp_f f g.
    p.have("pq_app: Proof_Q (append_l p2 p1) (Imp_f f g)").by(
        PROOF_Q_APPEND, "p2", "Imp_f f g", "pq2", "p1", "f", "pq1"
    )
    p.have("tail_ex: ?h_inner. Proof_Q (append_l p2 p1) h_inner").by_witness(
        "Imp_f f g", "pq_app"
    )
    p.have(
        "tail_disj: (append_l p2 p1) = nil_l "
        "\\/ ?h_inner. Proof_Q (append_l p2 p1) h_inner"
    ).by_disj("tail_ex")

    target_eq = SPECL([g_t, app_t, g_t], PROOF_Q_AT_CONS)
    p.have(
        "target_body: g = g "
        "/\\ valid_step (append_l p2 p1) g "
        "/\\ ((append_l p2 p1) = nil_l "
        "\\/ ?h_inner. Proof_Q (append_l p2 p1) h_inner)"
    ).by_thm(
        CONJ(
            REFL(g_t),
            CONJ(p.fact("valid_th"), p.fact("tail_disj")),
        )
    )
    p.have("pq_witness: Proof_Q (cons_l g (append_l p2 p1)) g").by_eq_mp(
        SYM(target_eq), "target_body"
    )
    p.thus("?p. Proof_Q p g").by_witness("cons_l g (append_l p2 p1)", "pq_witness")


# ---------------------------------------------------------------------------
# Stage 3B (j) -- Sigma_1 definition of Prov_Q.
#
#   Prov_Q n  :<=>  ?p. Proof_Q p n.
#
# This is the canonical form: provability is the existence of an
# explicit list-of-formulas proof. The closure rules under axioms,
# modus ponens, and generalisation are derived from AXIOM_HAS_PROOF,
# MP_HAS_PROOF, GEN_HAS_PROOF below.
# ---------------------------------------------------------------------------


PROV_Q_DEF = define(
    "Prov_Q",
    parse_type("nat0 -> bool"),
    "\\n:nat0. ?p:nat0. Proof_Q p n",
)
Prov_Q = mk_const("Prov_Q", [])
# |- !n. Prov_Q n = (?p. Proof_Q p n).
PROV_Q_AT = _at1(PROV_Q_DEF, _n_n0)


# ---------------------------------------------------------------------------
# Stage 3B (k) -- closure rules.
#
#   (1) |- !n. is_axiom n ==> Prov_Q n.
#   (2) |- !f g. Prov_Q f /\ Prov_Q (Imp_f f g) ==> Prov_Q g.
#   (3) |- !f x. Prov_Q f ==> Prov_Q (Forall_f x f).
#
# Each one is the corresponding *_HAS_PROOF lemma packaged through
# PROV_Q_AT (which folds ``?p. Proof_Q p _`` into ``Prov_Q _``).
# ---------------------------------------------------------------------------


@proof
def PROV_Q_AXIOM(p):
    """|- !n. is_axiom n ==> Prov_Q n."""
    p.goal("!n. is_axiom n ==> Prov_Q n")
    p.fix("n")
    p.assume("ax: is_axiom n")
    p.have("ex: ?p. Proof_Q p n").by(AXIOM_HAS_PROOF, "n", "ax")
    pq_at_n = SPEC(p._parse("n"), PROV_Q_AT)
    p.thus("Prov_Q n").by_eq_mp(SYM(pq_at_n), "ex")


@proof
def PROV_Q_MP(p):
    """|- !f g. Prov_Q f /\\ Prov_Q (Imp_f f g) ==> Prov_Q g."""
    p.goal("!f g. (Prov_Q f /\\ Prov_Q (Imp_f f g)) ==> Prov_Q g")
    p.fix("f g")
    p.assume("(pf, pfg): Prov_Q f /\\ Prov_Q (Imp_f f g)")
    pq_at_f = SPEC(p._parse("f"), PROV_Q_AT)
    pq_at_fg = SPEC(p._parse("Imp_f f g"), PROV_Q_AT)
    pq_at_g = SPEC(p._parse("g"), PROV_Q_AT)
    p.have("ex_f: ?p. Proof_Q p f").by_eq_mp(pq_at_f, "pf")
    p.have("ex_fg: ?p. Proof_Q p (Imp_f f g)").by_eq_mp(pq_at_fg, "pfg")
    p.have("ex_g: ?p. Proof_Q p g").by(
        MP_HAS_PROOF, "f", "g", CONJ(p.fact("ex_f"), p.fact("ex_fg"))
    )
    p.thus("Prov_Q g").by_eq_mp(SYM(pq_at_g), "ex_g")


@proof
def PROV_Q_GEN(p):
    """|- !f x. Prov_Q f ==> Prov_Q (Forall_f x f)."""
    p.goal("!f x. Prov_Q f ==> Prov_Q (Forall_f x f)")
    p.fix("f x")
    p.assume("pf: Prov_Q f")
    pq_at_f = SPEC(p._parse("f"), PROV_Q_AT)
    pq_at_fx = SPEC(p._parse("Forall_f x f"), PROV_Q_AT)
    p.have("ex_f: ?p. Proof_Q p f").by_eq_mp(pq_at_f, "pf")
    p.have("ex_fx: ?p. Proof_Q p (Forall_f x f)").by(
        GEN_HAS_PROOF, "f", "x", "ex_f"
    )
    p.thus("Prov_Q (Forall_f x f)").by_eq_mp(SYM(pq_at_fx), "ex_fx")


# ---------------------------------------------------------------------------
# Stage 3B (l) -- the equivalence ``Prov_Q n <=> ?p. Proof_Q p n``.
#
# It is the defining equation, packaged via ``PROV_Q_AT``. Kept under
# the historic name so downstream code that imports
# ``PROV_Q_IFF_PROOF_Q`` keeps working.
# ---------------------------------------------------------------------------


PROV_Q_IFF_PROOF_Q = PROV_Q_AT


# ---------------------------------------------------------------------------
# Stage 3B (m) -- representability scaffolding.
#
# A unary predicate ``P : nat0 -> bool`` is *represented* by a
# Q-formula ``F`` (a nat0 godelnum, taken to be a Q-formula whose only
# free variable is ``var_x``) iff:
#
#   * (positive)  !n. P n      ==> Prov_Q (substitute F (numeral n) var_x).
#   * (negative)  !n. ~ P n    ==> Prov_Q (Not_f (substitute F (numeral n) var_x)).
#
# We package the conjunction of the two conditions as
# ``represents_pred F P``. Defined here, after ``Prov_Q``.
# ---------------------------------------------------------------------------


_pos_clause = mk_forall(
    _n_n0,
    mk_imp(mk_app(_P_pred, _n_n0), mk_app(Prov_Q, _subst_at_numeral(_F_n0, _n_n0))),
)
_neg_clause = mk_forall(
    _n_n0,
    mk_imp(
        mk_not(mk_app(_P_pred, _n_n0)),
        mk_app(Prov_Q, mk_app(Not_f, _subst_at_numeral(_F_n0, _n_n0))),
    ),
)

_represents_pred_body = mk_and(_pos_clause, _neg_clause)

REPRESENTS_PRED_DEF = define(
    "represents_pred",
    parse_type("nat0 -> (nat0 -> bool) -> bool"),
    mk_abs(_F_n0, mk_abs(_P_pred, _represents_pred_body)),
)
represents_pred = mk_const("represents_pred", [])


# |- !F P. represents_pred F P =
#          ((!n. P n ==> Prov_Q (substitute F (numeral n) var_x))
#        /\ (!n. ~ P n
#               ==> Prov_Q (Not_f (substitute F (numeral n) var_x)))).
REPRESENTS_PRED_AT = _at2(REPRESENTS_PRED_DEF, _F_n0, _P_pred)


# ---------------------------------------------------------------------------
# Stage 3C (a) -- representability of ``substitute`` (AXIOMATIZED).
#
# Headline theorem (``SUBSTITUTE_REPRESENTS``):
#   |- !F t v. Prov_Q (
#         substitute (substitute (substitute (substitute
#             substitute_internal (numeral F) var_x)
#             (numeral t) var_y)
#             (numeral v) var_z)
#             (numeral (substitute F t v)) var_w).
#
# ``substitute_internal`` is a Q-formula in four free variables -- ``var_x``
# (F-slot), ``var_y`` (t-slot), ``var_z`` (v-slot), ``var_w`` (result-slot)
# -- expressing the relation "substitute(F, t, v) = r".
#
# The standard textbook proof requires:
#   * a finite-sequence coding device inside Q (Goedel's beta function
#     via Chinese remainder, or Cantor pairing via division/mod);
#   * external structural induction on F using the Stage-1 SUBSTITUTE_AT_*
#     equations.
#
# Why a single fixed Sigma_1 formula is required, not a HOL-recursive
# family: the diagonal lemma (Stage 3D) forms the Goedel sentence by
# substituting a numeric godelnum into a *single fixed* internal-provability
# formula. Without ``substitute_internal`` as one fixed Q-formula, no
# ``D(x, y)`` represents the diagonal function and the fixed-point
# construction collapses (analysis recorded for posterity, do not
# re-explore).
#
# AXIOMATIZED for now: ``substitute_internal`` is declared opaque
# (``new_constant``, no defining body) and ``SUBSTITUTE_REPRESENTS`` is
# closed via ``p.sorry()`` -- which posts ``new_axiom`` of the conclusion
# and prints a sorry-warning at proof end. The opaque declaration prevents
# downstream code from accidentally unfolding the placeholder and deriving
# inconsistencies from a degenerate body.
#
# To discharge later: build (Cantor pairing or beta) sequence coding,
# prove the substitute trace as a Sigma_1 predicate, then external
# induction on F (~1500 lines of new infrastructure including the arith.
# representability prerequisites for ``add``, ``times``, ``mod``).
#
# Planned alternative discharge path (Q + HF strengthening; see the
# PROPOSED EXTENSION block at the end of q_proof.py's Q-axiom list):
#
#   * Add Insert_t / In_a / Empty_t to Q's signature, plus axioms
#     Q8-Q12 mirroring NOT_IN_EMPTY / IN_INSERT_SAME / IN_INSERT_DIFF /
#     IN_EXT / IN_LT from hf_sets.py.
#   * ``substitute_internal`` is then the Sigma_1 predicate
#         ?T. is_substitute_trace T F t v r
#     where T : nat0 is an HF set of (subterm-shape, output-shape)
#     pairs (Pair_ord-encoded), and is_substitute_trace asserts:
#       (i)   the input pair (F, r) is in T;
#       (ii)  every (a, b) in T satisfies the structural-recursion
#             clause matching ``substitute``'s SUBSTITUTE_AT_*
#             equations -- a bounded conjunction over its members
#             via In, decoded by Pair_ord projection.
#   * Q proves ``substitute_internal (numeral F) (numeral t) (numeral v)
#     (numeral (substitute F t v))`` at every numeral instance by
#     exhibiting the trace HF set explicitly (it has |F|-many
#     elements, each one a closed Pair_ord numeral); the verification
#     conjuncts are decidable equalities + In-membership facts, all
#     Sigma_0 in Q + HF.
#   * Lines: ~150 vs ~1500 in the beta-function path.
# ---------------------------------------------------------------------------


VAR_Z_DEF = define("var_z", parse_type("nat0"), "Var_t (SUC0 (SUC0 0))")
var_z = mk_const("var_z", [])

VAR_W_DEF = define("var_w", parse_type("nat0"), "Var_t (SUC0 (SUC0 (SUC0 0)))")
var_w = mk_const("var_w", [])


# Opaque: no defining body. Stage 3C will replace this with a definition
# of the actual Sigma_1 substitute-trace formula.
new_constant("substitute_internal", nat0_ty)
substitute_internal = mk_const("substitute_internal", [])


@proof
def SUBSTITUTE_REPRESENTS(p):
    """|- !F t v. Prov_Q (
              substitute (substitute (substitute (substitute
                  substitute_internal (numeral F) var_x)
                  (numeral t) var_y)
                  (numeral v) var_z)
                  (numeral (substitute F t v)) var_w).

    Stage 3C(a) representability of ``substitute``. AXIOMATIZED via
    ``p.sorry()``; see Stage 3C section comment for the deferred
    construction (Cantor pairing or beta function + induction on F).
    """
    p.goal(
        "!F t v. Prov_Q ("
        "substitute (substitute (substitute (substitute "
        "  substitute_internal (numeral F) var_x) "
        "  (numeral t) var_y) "
        "  (numeral v) var_z) "
        "  (numeral (substitute F t v)) var_w)"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 3D (a) -- representability of provability (AXIOMATIZED).
#
# Headline theorem (``PROV_Q_REPRESENTS``):
#   |- !n. Prov_Q n <=>
#          Prov_Q (substitute Prov_Q_internal (numeral n) var_x).
#
# ``Prov_Q_internal`` is a Q-formula with ``var_x`` as its sole free
# variable, expressing the relation "Prov_Q holds at var_x".
#
# The standard textbook construction (BBJ Ch. 17, Smullyan Ch. 4) goes
# bottom-up:
#
#   * ``mem_l_internal``    -- representability of HOL ``mem_l``
#   * ``valid_step_internal`` -- representability of HOL ``valid_step``
#                                (built from ``mem_l_internal``,
#                                ``is_axiom_internal``,
#                                ``is_mp_internal``,
#                                ``is_gen_internal``)
#   * ``Proof_Q_internal``  -- representability of HOL ``Proof_Q``
#                                (recursive over the proof list;
#                                requires sequence coding via beta or
#                                Cantor pairing inside Q)
#   * ``Prov_Q_internal``   -- existential closure
#                                ?_internal var_y. Proof_Q_internal,
#                                where ``?_internal`` is encoded in Q
#                                as ``Not_f (Forall_f (var_y_idx)
#                                (Not_f ...))`` since Q's only native
#                                quantifier is ``Forall_f``.
#
# Forward direction (HOL ``Prov_Q n`` ==> Q proves
# ``Prov_Q_internal``-substituted): Sigma_1 completeness for Q (any true
# Sigma_1 sentence is Q-provable). Computed externally via
# ``PROV_Q_IFF_PROOF_Q`` to extract a witness ``p``, then witnessed
# internally.
#
# Backward direction (Q proves ==> HOL): Sigma_1 soundness for Q,
# which lives in Stage 6 via the HF model construction.
#
# AXIOMATIZED for now: ``Prov_Q_internal`` is declared opaque
# (``new_constant``, no defining body) and the headline theorem +
# diagonal-lemma side conditions (``is_form``, ``free_in``) are closed
# via ``p.sorry()``. The opaque declaration prevents accidental
# unfolding.
#
# Side conditions posted with the headline:
#   * ``IS_FORM_PROV_Q_INTERNAL``  : |- is_form Prov_Q_internal.
#   * ``FREE_IN_PROV_Q_INTERNAL``  : |- !v. free_in Prov_Q_internal v
#                                          <=> v = var_x.
# Both are required by the diagonal lemma (Stage 4): ``phi(x)`` must be
# a well-formed Q-formula whose only free variable is ``var_x``.
#
# Also defines ``substitute_2`` as a HOL helper for the diagonal lemma:
#   substitute_2 F a b vx vy := substitute (substitute F a vx) b vy.
#
# Planned alternative discharge path (Q + HF strengthening; see the
# PROPOSED EXTENSION block at the end of q_proof.py's Q-axiom list).
# Now that Prov_Q has been collapsed to ``\n. ?p. Proof_Q p n``, the
# Q-internal form is forced to be the existential closure
#   Prov_Q_internal(x) := ?_internal y. Proof_Q_internal(y, x).
# Under the HF strengthening:
#
#   * ``mem_l_internal`` collapses to ``In_a`` -- proof lists are HF
#     sets; "p has formula f" is just membership. (~5 lines vs the
#     ~200-line list-recursion encoding in the beta-function path.)
#   * ``valid_step_internal`` is the Sigma_0 disjunction
#         is_axiom_internal h \/
#         (?f1 f2. In f1 t /\ In f2 t /\ is_mp_internal f1 f2 h) \/
#         (?f1. In f1 t /\ is_gen_internal f1 h)
#     directly mirroring the HOL ``valid_step`` in this file.
#   * ``Proof_Q_internal(p, n)`` is then the conjunction over members
#     of the HF set p -- bounded by p itself via foundation Q12 --
#     plus a designated-head clause picking out n. Sigma_1; not
#     recursive because the HF foundation axiom bounds the search.
#   * Forward direction of PROV_Q_REPRESENTS: extract a Proof_Q
#     witness via PROV_Q_AT, exhibit its HF encoding as a Q-numeral,
#     verify the conjuncts term-by-term (each one a closed Sigma_0
#     fact Q proves at numerals).
#   * Backward direction (Q proves ==> HOL): unchanged -- Stage 6
#     HF |= (Q + Q8-Q12) is one HOL theorem citation per axiom.
#
# Lines: ~150 vs ~1500 in the beta-function path. Side conditions
# IS_FORM and FREE_IN become routine once Prov_Q_internal has its
# defining body, both decided by the same syntactic recursion that
# verified is_form for the connectives in q_syntax.py.
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
# bottom-up construction (Proof_Q_internal then existential closure).
new_constant("Prov_Q_internal", nat0_ty)
Prov_Q_internal = mk_const("Prov_Q_internal", [])


@proof
def PROV_Q_REPRESENTS(p):
    """|- !n. Prov_Q n <=>
              Prov_Q (substitute Prov_Q_internal (numeral n) var_x).

    Stage 3D(a) representability of ``Prov_Q``. AXIOMATIZED via
    ``p.sorry()``; see Stage 3D section comment for the deferred
    construction (Proof_Q_internal + Sigma_1 completeness/soundness).
    """
    p.goal("!n. Prov_Q n = Prov_Q (substitute Prov_Q_internal (numeral n) var_x)")
    p.sorry()


@proof
def IS_FORM_PROV_Q_INTERNAL(p):
    """|- is_form Prov_Q_internal.

    Side condition for the diagonal lemma. AXIOMATIZED via
    ``p.sorry()``; in the full construction, follows from the bottom-up
    build of ``Prov_Q_internal`` from ``Proof_Q_internal`` and the
    closure of ``is_form`` under the Q-formula constructors.
    """
    p.goal("is_form Prov_Q_internal")
    p.sorry()


@proof
def FREE_IN_PROV_Q_INTERNAL(p):
    """|- !v. free_in Prov_Q_internal v <=> v = var_x.

    Side condition for the diagonal lemma. AXIOMATIZED via
    ``p.sorry()``; ``var_x`` is the F-slot in the substitute-via-numeral
    representation pattern.
    """
    p.goal(
        "!v. free_in Prov_Q_internal v = (v = var_x)",
    )
    p.sorry()


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
    print()
    print("Stage 3B (d) -- list concatenation append_l.")
    print("    APPEND_L_DEF     :", pp_thm(APPEND_L_DEF))
    print("    APPEND_L_REC     :", pp_thm(APPEND_L_REC))
    print("    APPEND_L_AT_NIL  :", pp_thm(APPEND_L_AT_NIL))
    print("    APPEND_L_AT_CONS :", pp_thm(APPEND_L_AT_CONS))
    print()
    print("Stage 3B (e-g) -- preservation lemmas.")
    print("    MEM_L_APPEND_PRESERVES :", pp_thm(MEM_L_APPEND_PRESERVES))
    print("    VALID_STEP_PRESERVES   :", pp_thm(VALID_STEP_PRESERVES))
    print("    PROOF_Q_APPEND         :", pp_thm(PROOF_Q_APPEND))
    print("    PROOF_Q_HEAD_MEM       :", pp_thm(PROOF_Q_HEAD_MEM))
    print()
    print("Stage 3B (i) -- proof witnesses for the closure rules.")
    print("    AXIOM_HAS_PROOF   :", pp_thm(AXIOM_HAS_PROOF))
    print("    GEN_HAS_PROOF     :", pp_thm(GEN_HAS_PROOF))
    print("    MP_HAS_PROOF      :", pp_thm(MP_HAS_PROOF))
    print()
    print("Stage 3B (j-l) -- Sigma_1 Prov_Q and closure rules.")
    print("    PROV_Q_DEF         :", pp_thm(PROV_Q_DEF))
    print("    PROV_Q_AT          :", pp_thm(PROV_Q_AT))
    print("    PROV_Q_AXIOM       :", pp_thm(PROV_Q_AXIOM))
    print("    PROV_Q_MP          :", pp_thm(PROV_Q_MP))
    print("    PROV_Q_GEN         :", pp_thm(PROV_Q_GEN))
    print("    PROV_Q_IFF_PROOF_Q :", pp_thm(PROV_Q_IFF_PROOF_Q))
    print()
    print("Stage 3B (m) -- representability scaffolding.")
    print("    REPRESENTS_PRED_DEF :", pp_thm(REPRESENTS_PRED_DEF))
    print("    REPRESENTS_PRED_AT  :", pp_thm(REPRESENTS_PRED_AT))
    print()
    print("Stage 3C (a) -- representability of substitute (SORRY).")
    print("    VAR_Z_DEF              :", pp_thm(VAR_Z_DEF))
    print("    VAR_W_DEF              :", pp_thm(VAR_W_DEF))
    print("    SUBSTITUTE_REPRESENTS  :", pp_thm(SUBSTITUTE_REPRESENTS))
    print()
    print("Stage 3D (a) -- representability of provability (SORRY).")
    print("    SUBSTITUTE_2_DEF        :", pp_thm(SUBSTITUTE_2_DEF))
    print("    PROV_Q_REPRESENTS       :", pp_thm(PROV_Q_REPRESENTS))
    print("    IS_FORM_PROV_Q_INTERNAL :", pp_thm(IS_FORM_PROV_Q_INTERNAL))
    print("    FREE_IN_PROV_Q_INTERNAL :", pp_thm(FREE_IN_PROV_Q_INTERNAL))
