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
from nat0 import nat0_ty, define_unary_0, mk_suc0, ZERO
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
    Var_t,  # noqa: F401  -- parser alias for is_substitute_step
    Plus_t,  # noqa: F401  -- parser alias for is_substitute_step
    Times_t,  # noqa: F401  -- parser alias for is_substitute_step
    Eq_f,  # noqa: F401  -- parser alias for is_substitute_step
    Not_f,  # noqa: F401  -- parser alias for is_substitute_step
    Imp_f,  # noqa: F401  -- parser alias for is_substitute_step
    Forall_f,  # noqa: F401  -- parser alias for is_substitute_step
    Insert_t,  # noqa: F401  -- parser alias for is_substitute_step
    In_a,  # noqa: F401  -- parser alias for is_substitute_step
    IS_TERM_REC,
    IS_TERM_AT_SUCC,
    SUBSTITUTE_AT_NOT,
    SUBSTITUTE_AT_IMP,
    SUBSTITUTE_AT_EQ,
    SUBSTITUTE_AT_FORALL_HIT,
    SUBSTITUTE_AT_FORALL_MISS,
    mono_iff_eq_or_pw_step,
    _unfold_rec_via_F_def,
    _extract_nfg,
    _mono_iff_value_binary_pw_step,
)
from hf_sets import (
    In,  # noqa: F401  -- parser alias for is_substitute_step
    Pair_ord,  # noqa: F401  -- parser alias for is_substitute_step
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
    VAR_Z_DEF,
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


is_term = mk_const("is_term", [])


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
# TODO -- discharge via Q + HF (preferred over the beta-function path).
# The HF primitives (Insert_t / In_a / Empty_t) and axioms Q8-Q12 are
# already in place (q_syntax.py, q_proof.py). Define
# ``substitute_internal`` as the Sigma_1 predicate
#     ?T. is_substitute_trace T F t v r
# where T : nat0 is an HF set of (subterm-shape, output-shape) pairs
# (Pair_ord-encoded), and is_substitute_trace asserts:
#   (i)  the input pair (F, r) is in T;
#   (ii) every (a, b) in T satisfies the structural-recursion clause
#        matching substitute's SUBSTITUTE_AT_* equations -- a bounded
#        conjunction over its members via In, decoded by Pair_ord
#        projection.
# Q proves substitute_internal at every numeral instance by exhibiting
# the trace HF set explicitly (|F|-many closed Pair_ord numerals);
# verification conjuncts are decidable equalities + In-membership
# facts, all Sigma_0 in Q + HF. Estimated ~150 lines vs ~1500 for the
# beta-function path. The structural recognisers in q_syntax.py
# (is_term, is_form, free_in, substitute) already cover Insert_t and
# In_a, so this can be attempted directly.
#
# Progress (2026-05-09):
#   * Union added to hf_sets.py (Stage 3 cont.) with IN_UNION.
#   * var_T (Var_t 4) and var_a..var_f2 (Var_t 5..15) added as the
#     internal Q-variable indices used by the trace-encoding formula.
#   * is_substitute_step (HOL) and is_substitute_trace (HOL) defined,
#     with pointwise unfolding lemmas IS_SUBSTITUTE_STEP_AT and
#     IS_SUBSTITUTE_TRACE_AT.
#   * TRACE_STEP_MONO proved -- membership-monotonicity of
#     is_substitute_step (the foundation for binary trace assembly via
#     ``Insert (Pair_ord F r) (Union T1 T2)``).
#   * Q_and / Q_or / Q_exists / Q_imp / ... Python-level helpers for
#     building Q-formulas compositionally (Q has only Forall_f / Imp_f
#     / Not_f / Eq_f as primitives -- these macros suppress the
#     bookkeeping bloat of explicit Not_f/Imp_f trees).
#   * TRACE_EXISTS stated under syntactic precondition (is_term F \/
#     is_form F) and SORRY'd. Full proof is mechanical follow-up:
#     strong induction on F via nat0_lt; the 13 SUBSTITUTE_AT_* cases
#     each construct ``Insert (Pair_ord F (substitute F t v))
#     (Union T_sub1 T_sub2 ...)`` over IH-supplied sub-traces and
#     verify is_substitute_trace via TRACE_STEP_MONO + IN_UNION +
#     IN_INSERT.
#
# Remaining significant scope (B1-B3):
#
#   B1 (Q-encoding):  is_substitute_step_internal as a closed Q-formula
#     blocks on Sigma_1 representability of ``Pair_ord`` and ``In``
#     (neither is in Q's primitive vocabulary -- ``Pair_ord`` is an
#     HF helper, ``In`` is bit-extraction). Each disjunct of
#     is_substitute_step references ``In (Pair_ord _ _) T`` and
#     constructor patterns ``a = Var_t v / Plus_t a1 a2 / ...`` which
#     all involve ``Pair_ord`` (since each Q-syntax constructor
#     unfolds to a ``Pair_ord``-prefixed encoding). Without
#     representing-formula constants ``is_Pair_ord_internal``,
#     ``is_In_internal`` (or inlined Sigma_1-equivalent expansions),
#     the Q-formula cannot be spelled out. Each representability
#     proof is its own ~50-100 line construction (size lemmas, strict
#     monotonicity, the Sigma_0 verification at numerals).
#
#   B2 (replace opaque substitute_internal):  Becomes one ``define``
#     call once B1's is_substitute_trace_internal is in hand. Trivial
#     in isolation; blocked on B1.
#
#   B3 (SUBSTITUTE_REPRESENTS proof):  Combines TRACE_EXISTS (A4) with
#     B1's Q-encoding, exhibiting the trace HF set T and discharging
#     each disjunct's Sigma_0 verification using Q + HF axioms. Blocks
#     on A4 + B1 + B2; itself ~200-300 lines (mostly Q-axiom citations).
#
# Total remaining estimate after foundations: ~500-1000 lines, plus
# the Pair_ord / In representability prerequisites (~200 lines).
# ---------------------------------------------------------------------------


VAR_W_DEF = define("var_w", parse_type("nat0"), "Var_t (SUC0 (SUC0 (SUC0 0)))")
var_w = mk_const("var_w", [])


# var_T -- Q-internal bound variable for the existentially-quantified HF
# trace set inside ``substitute_internal``. Index 4 (SUC0^4 0); the four
# free slots var_x/y/z/w (indices 0..3) are reserved for the input/output
# pair (F, t, v, r).
VAR_T_DEF = define(
    "var_T",
    parse_type("nat0"),
    "Var_t (SUC0 (SUC0 (SUC0 (SUC0 0))))",
)
var_T = mk_const("var_T", [])


# Additional Q-internal variables for the body of is_substitute_trace_internal:
#   var_a, var_b           -- the "!a b. ..." outer for-all binders.
#   var_s1, var_s2         -- Succ_t / Not_f sub-shape existentials.
#   var_wq                 -- Var_t-miss / Forall_f-* index existentials
#                             (named with q-suffix to avoid clash with HOL w).
#   var_a1, var_a2,        -- binary-constructor sub-shape existentials.
#   var_b1, var_b2
#   var_f1, var_f2         -- Forall_f-miss body existentials.
# Indices 5..14 of the Q-variable namespace.
def _var_q_def(name, idx):
    suc = "0"
    for _ in range(idx):
        suc = f"(SUC0 {suc})"
    return define(name, parse_type("nat0"), f"Var_t {suc}")


VAR_A_DEF = _var_q_def("var_a", 5)
var_a = mk_const("var_a", [])
VAR_B_DEF = _var_q_def("var_b", 6)
var_b = mk_const("var_b", [])
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


# Q-encoding macros at the Python level. Q has only Forall_f, Imp_f, Not_f,
# Eq_f as primitives -- everything else is hand-encoded. Build Q-formulas
# compositionally rather than spelling out the Not_f/Imp_f/Forall_f tree
# literally (which would balloon any large Q-formula by 10x).
def Q_and(a, b):
    """Q's /\\ as Not_f (Imp_f a (Not_f b))."""
    return mk_app(Not_f, mk_app(Imp_f, a, mk_app(Not_f, b)))


def Q_or(a, b):
    """Q's \\/ as Imp_f (Not_f a) b."""
    return mk_app(Imp_f, mk_app(Not_f, a), b)


def Q_imp(a, b):
    """Q's ==> -- Imp_f a b."""
    return mk_app(Imp_f, a, b)


def Q_not(a):
    return mk_app(Not_f, a)


def Q_eq(a, b):
    return mk_app(Eq_f, a, b)


def Q_neq(a, b):
    return Q_not(Q_eq(a, b))


def Q_forall(idx, body):
    """Q's !x. body  --  Forall_f idx body  (idx is the raw nat0 index)."""
    return mk_app(Forall_f, idx, body)


def Q_exists(idx, body):
    """Q's ?x. body  --  Not_f (Forall_f idx (Not_f body))."""
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
    """Nested Q-exists ``?idx0 idx1 ... . body``."""
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
# Substitute-pushing lemmas for the Q-encoding macros.
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
def SUBSTITUTE_Q_AND(p):
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
def SUBSTITUTE_Q_OR(p):
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
def SUBSTITUTE_Q_NEQ(p):
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
def SUBSTITUTE_Q_EXISTS_HIT(p):
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
def SUBSTITUTE_Q_EXISTS_MISS(p):
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
# of the 13 SUBSTITUTE_AT_* clauses with respect to the substitution
# parameters (t, v) and a trace HF set T:
#   * Constant-shape clauses (Zero_t, Var_t at v, Var_t off v, Forall_f
#     hit) require no trace consultations -- b is determined by a alone.
#   * Recursive clauses (Succ_t / Not_f, the binary constructors, and
#     Forall_f miss) require the corresponding sub-shape pairs to be in T,
#     witnessed via In (Pair_ord _ _) T.
#
# This predicate is the HOL counterpart of the Q-formula
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


IS_SUBSTITUTE_STEP_DEF = define(
    "is_substitute_step",
    parse_type("nat0 -> nat0 -> nat0 -> nat0 -> nat0 -> bool"),
    "\\T:nat0. \\t:nat0. \\v:nat0. \\a:nat0. \\b:nat0. "
    "(a = Zero_t /\\ b = Zero_t) "
    "\\/ (?s1 s2. a = Succ_t s1 /\\ b = Succ_t s2 /\\ In (Pair_ord s1 s2) T) "
    "\\/ (a = Var_t v /\\ b = t) "
    "\\/ (?w. a = Var_t w /\\ ~(w = v) /\\ b = Var_t w) "
    "\\/ (?a1 a2 b1 b2. a = Plus_t a1 a2 /\\ b = Plus_t b1 b2 "
    "      /\\ In (Pair_ord a1 b1) T /\\ In (Pair_ord a2 b2) T) "
    "\\/ (?a1 a2 b1 b2. a = Times_t a1 a2 /\\ b = Times_t b1 b2 "
    "      /\\ In (Pair_ord a1 b1) T /\\ In (Pair_ord a2 b2) T) "
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


# Pointwise: |- !T t v a b. is_substitute_step T t v a b = body[T,t,v,a,b].
def _build_is_substitute_step_at():
    from tactics import AP_THM, BETA_CONV, TRANS, GENL

    th = IS_SUBSTITUTE_STEP_DEF
    args = [_T_step, _t_step, _v_step, _a_step, _b_step]
    for x in args:
        th = AP_THM(th, x)
        th = TRANS(th, BETA_CONV(rand(th._concl)))
    return GENL(args, th)


IS_SUBSTITUTE_STEP_AT = _build_is_substitute_step_at()


# Pointwise unfolding helper for n-ary curried definitions: given
# ``def_th : c = \x1 ... xn. body``, produce
# ``|- !x1 ... xn. c x1 ... xn = body[xi]``.
def _at_n(def_th, args):
    from tactics import AP_THM, BETA_CONV, TRANS, GENL

    th = def_th
    for x in args:
        th = AP_THM(th, x)
        th = TRANS(th, BETA_CONV(rand(th._concl)))
    return GENL(list(args), th)


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


IS_SUBSTITUTE_TRACE_DEF = define(
    "is_substitute_trace",
    parse_type("nat0 -> nat0 -> nat0 -> nat0 -> nat0 -> bool"),
    "\\T:nat0. \\F:nat0. \\t:nat0. \\v:nat0. \\r:nat0. "
    "In (Pair_ord F r) T "
    "/\\ (!a b. In (Pair_ord a b) T ==> is_substitute_step T t v a b)",
)
is_substitute_trace = mk_const("is_substitute_trace", [])


# Pointwise: |- !T F t v r. is_substitute_trace T F t v r =
#                          In (Pair_ord F r) T /\
#                          (!a b. In (Pair_ord a b) T ==>
#                                 is_substitute_step T t v a b).
IS_SUBSTITUTE_TRACE_AT = _at_n(
    IS_SUBSTITUTE_TRACE_DEF,
    [_T_n0, _F_n0, _tt_n0, _vv_n0, _rr_n0],
)


# String-templated 13-disjunction body of is_substitute_step, with the
# trace HF set ``T`` substituted in. Used by TRACE_STEP_MONO so the same
# disjunction can be referenced under both T1 and T2 without copy-paste.
def _is_step_body(T):
    return (
        f"(a = Zero_t /\\ b = Zero_t) "
        f"\\/ (?s1 s2. a = Succ_t s1 /\\ b = Succ_t s2 "
        f"      /\\ In (Pair_ord s1 s2) {T}) "
        f"\\/ (a = Var_t v /\\ b = t) "
        f"\\/ (?w. a = Var_t w /\\ ~(w = v) /\\ b = Var_t w) "
        f"\\/ (?a1 a2 b1 b2. a = Plus_t a1 a2 /\\ b = Plus_t b1 b2 "
        f"      /\\ In (Pair_ord a1 b1) {T} /\\ In (Pair_ord a2 b2) {T}) "
        f"\\/ (?a1 a2 b1 b2. a = Times_t a1 a2 /\\ b = Times_t b1 b2 "
        f"      /\\ In (Pair_ord a1 b1) {T} /\\ In (Pair_ord a2 b2) {T}) "
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
            # 1. Zero_t (atomic).
            with p.case("c1: a = Zero_t /\\ b = Zero_t"):
                p.thus(body_T2).by_disj("c1")
            # 2. Succ_t (unary recursive).
            with p.case(
                "c2: ?s1 s2. a = Succ_t s1 /\\ b = Succ_t s2 "
                "/\\ In (Pair_ord s1 s2) T1"
            ):
                # case auto-chooses outer s1; s1_eq: ?s2. body[s1, s2].
                p.choose("s2", "s1_eq")
                p.split("s2_eq", "(c2a, c2b, c2_in1)")
                p.have("c2_in2: In (Pair_ord s1 s2) T2").by(
                    "hsub", "Pair_ord s1 s2", "c2_in1"
                )
                p.have(
                    "c2d: ?s1 s2. a = Succ_t s1 /\\ b = Succ_t s2 "
                    "/\\ In (Pair_ord s1 s2) T2"
                ).by_exists(["s1", "s2"], "c2a", "c2b", "c2_in2")
                p.thus(body_T2).by_disj("c2d")
            # 3. Var_t hit (atomic).
            with p.case("c3: a = Var_t v /\\ b = t"):
                p.thus(body_T2).by_disj("c3")
            # 4. Var_t miss (existential, no In).
            with p.case(
                "c4: ?w. a = Var_t w /\\ ~(w = v) /\\ b = Var_t w"
            ):
                p.thus(body_T2).by_disj("c4")
            # 5. Plus_t (binary recursive).
            with p.case(
                "c5: ?a1 a2 b1 b2. a = Plus_t a1 a2 /\\ b = Plus_t b1 b2 "
                "/\\ In (Pair_ord a1 b1) T1 /\\ In (Pair_ord a2 b2) T1"
            ):
                p.choose("a2", "a1_eq")
                p.choose("b1", "a2_eq")
                p.choose("b2", "b1_eq")
                p.split("b2_eq", "(c5a, c5b, c5_in1, c5_in2)")
                p.have("c5_in1_T2: In (Pair_ord a1 b1) T2").by(
                    "hsub", "Pair_ord a1 b1", "c5_in1"
                )
                p.have("c5_in2_T2: In (Pair_ord a2 b2) T2").by(
                    "hsub", "Pair_ord a2 b2", "c5_in2"
                )
                p.have(
                    "c5d: ?a1 a2 b1 b2. a = Plus_t a1 a2 /\\ b = Plus_t b1 b2 "
                    "/\\ In (Pair_ord a1 b1) T2 /\\ In (Pair_ord a2 b2) T2"
                ).by_exists(
                    ["a1", "a2", "b1", "b2"],
                    "c5a", "c5b", "c5_in1_T2", "c5_in2_T2",
                )
                p.thus(body_T2).by_disj("c5d")
            # 6. Times_t (binary recursive).
            with p.case(
                "c6: ?a1 a2 b1 b2. a = Times_t a1 a2 /\\ b = Times_t b1 b2 "
                "/\\ In (Pair_ord a1 b1) T1 /\\ In (Pair_ord a2 b2) T1"
            ):
                p.choose("a2", "a1_eq")
                p.choose("b1", "a2_eq")
                p.choose("b2", "b1_eq")
                p.split("b2_eq", "(c6a, c6b, c6_in1, c6_in2)")
                p.have("c6_in1_T2: In (Pair_ord a1 b1) T2").by(
                    "hsub", "Pair_ord a1 b1", "c6_in1"
                )
                p.have("c6_in2_T2: In (Pair_ord a2 b2) T2").by(
                    "hsub", "Pair_ord a2 b2", "c6_in2"
                )
                p.have(
                    "c6d: ?a1 a2 b1 b2. a = Times_t a1 a2 /\\ b = Times_t b1 b2 "
                    "/\\ In (Pair_ord a1 b1) T2 /\\ In (Pair_ord a2 b2) T2"
                ).by_exists(
                    ["a1", "a2", "b1", "b2"],
                    "c6a", "c6b", "c6_in1_T2", "c6_in2_T2",
                )
                p.thus(body_T2).by_disj("c6d")
            # 7. Eq_f (binary recursive).
            with p.case(
                "c7: ?a1 a2 b1 b2. a = Eq_f a1 a2 /\\ b = Eq_f b1 b2 "
                "/\\ In (Pair_ord a1 b1) T1 /\\ In (Pair_ord a2 b2) T1"
            ):
                p.choose("a2", "a1_eq")
                p.choose("b1", "a2_eq")
                p.choose("b2", "b1_eq")
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
                p.choose("s2", "s1_eq")
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
                p.choose("a2", "a1_eq")
                p.choose("b1", "a2_eq")
                p.choose("b2", "b1_eq")
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
                p.choose("f1", "w_eq")
                p.choose("f2", "f1_eq")
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
                p.choose("a2", "a1_eq")
                p.choose("b1", "a2_eq")
                p.choose("b2", "b1_eq")
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
                p.choose("a2", "a1_eq")
                p.choose("b1", "a2_eq")
                p.choose("b2", "b1_eq")
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
# TRACE_EXISTS -- trace existence for syntactic F.
#
#   |- !F t v. (is_term F \/ is_form F) ==>
#               ?T. is_substitute_trace T F t v (substitute F t v).
#
# Strong induction on F via nat0_lt; case-split on the is_term / is_form
# disjuncts to expose F's constructor shape; in each constructor case
# build the trace as ``Insert (Pair_ord F (substitute F t v))
# (Union T_sub1 T_sub2 ...)`` over IH-supplied sub-traces.
#
# 13 cases (one per SUBSTITUTE_AT_* clause) -- each ~50-100 lines in
# the obvious mechanical style: pattern-match F, recurse via IH on
# proper sub-formulas, lift inner is_substitute_step facts through
# TRACE_STEP_MONO across the Insert+Union extension. The pattern is
# uniform but verbose; the binary cases (Plus_t, Times_t, Eq_f, Imp_f,
# Insert_t, In_a) and Forall_f miss are the longest.
#
# Currently SORRY'd; the foundations (TRACE_STEP_MONO, IS_SUBSTITUTE_*_AT,
# Union/IN_UNION) are all in place so this is mechanical follow-up work.
# ---------------------------------------------------------------------------


@proof
def TRACE_EXISTS(p):
    p.goal(
        "!F t v. (is_term F \\/ is_form F) ==> "
        "?T. is_substitute_trace T F t v (substitute F t v)"
    )
    p.sorry()


# ===========================================================================
# Stubs for the Q-encoding side (B1).
#
# Each ``is_X_internal`` is the Q-formula encoding of the HOL predicate
# ``X``. The associated ``IS_X_REPRESENTS`` theorem says: at every closed
# numeral instance where the HOL fact holds, Q proves the substituted
# Q-formula. (Sigma_1 completeness applied to the specific Sigma_1
# statement.)
#
# All declared opaque (``new_constant``, no defining body) and SORRY'd to
# allow downstream construction (B3) to type-check while leaving the
# representability proofs as discrete follow-up tasks. Concrete bodies
# are spelled out in the docstrings; once filled in, replace the
# ``new_constant`` with ``define`` and drop the ``sorry``.
# ===========================================================================


# B1.0 (a) -- pow2 representability.
# Needed by Singleton (= pow2) and hence by Pair_ord. Sigma_1
# representability of the recursive function ``pow2 : nat0 -> nat0``.
new_constant("is_pow2_internal", nat0_ty)
is_pow2_internal = mk_const("is_pow2_internal", [])


@proof
def IS_POW2_REPRESENTS(p):
    """|- !x. Prov_Q (substitute (substitute is_pow2_internal
                       (numeral x) var_x)
                       (numeral (pow2 x)) var_y).

    SORRY. Construction (~80 lines):
      * Body: ?p. is_pow2_trace_internal p var_x var_y, where the trace
        p (HF set or sequence) records ``(i, pow2 i)`` for i = 0..x.
      * Trace clause: (0, 1) in p, and (i, k) in p for i > 0 implies
        (i-1, k/2) in p (i.e. each step applies double).
      * At numerals: exhibit the trace as ``Insert_t``-stacked closed
        Pair_ord numerals, all Sigma_0-verifiable in Q + HF.
    """
    p.goal(
        "!x. Prov_Q (substitute (substitute is_pow2_internal "
        "  (numeral x) var_x) "
        "  (numeral (pow2 x)) var_y)"
    )
    p.sorry()


# B1.0 (b) -- Pair_ord representability.
# Needed for the trace HF set: the trace consists of Pair_ord-encoded
# (sub-shape, output-shape) entries, and Q must prove each entry's shape
# at numerals.
new_constant("is_Pair_ord_internal", nat0_ty)
is_Pair_ord_internal = mk_const("is_Pair_ord_internal", [])


@proof
def IS_PAIR_ORD_REPRESENTS(p):
    """|- !x y. Prov_Q (substitute^3 is_Pair_ord_internal
                          (numeral x) var_x
                          (numeral y) var_y
                          (numeral (Pair_ord x y)) var_z).

    SORRY. Construction (~80 lines, on top of IS_POW2_REPRESENTS):
      Pair_ord x y = Pair (Singleton x) (Pair x y)
                    = Insert (pow2 x) (Insert x (pow2 y)).
      Body of is_Pair_ord_internal: the Q-formula stating that var_z is
      the result of two Insert_t applications wrapped around the pow2
      values of var_x and var_y. Composition of:
        * IS_POW2_REPRESENTS at var_x   (pow2 x = some w_x)
        * IS_POW2_REPRESENTS at var_y   (pow2 y = some w_y)
        * Sigma_0 verification of Insert_t (pow2 x) (Insert_t var_x (pow2 y))
          = var_z at closed numerals (decidable in Q + HF).
    """
    p.goal(
        "!x y. Prov_Q (substitute (substitute (substitute "
        "  is_Pair_ord_internal (numeral x) var_x) "
        "  (numeral y) var_y) "
        "  (numeral (Pair_ord x y)) var_z)"
    )
    p.sorry()


# B1.0 (c) -- In representability.
# Needed by every disjunct of is_substitute_step (which references
# ``In (Pair_ord _ _) T``) and by is_substitute_trace clause (i).
new_constant("is_In_internal", nat0_ty)
is_In_internal = mk_const("is_In_internal", [])


@proof
def IS_IN_REPRESENTS(p):
    """|- !x y. (In x y ==> Prov_Q (substitute^2 is_In_internal
                                       (numeral x) var_x
                                       (numeral y) var_y))
              /\\ (~In x y ==> Prov_Q (Not_f (substitute^2 is_In_internal
                                                (numeral x) var_x
                                                (numeral y) var_y))).

    SORRY. Both directions are Sigma_1 / Sigma_0-decidable since In x y
    = bit x y = ODD (HALF^x y), a primitive-recursive predicate decidable
    in Q + HF at closed numerals. Construction (~80 lines):
      * Body: a Sigma_1 trace formula recording the HALF chain
        y, HALF y, ..., HALF^x y, then asserting ODD of the last entry.
      * Forward: exhibit the trace at concrete x, y; verify each HALF
        step via Q's Q4-Q7 + HF Q8-Q12 axiom citations.
      * Negation: dual; use ~ODD (= Eq_f ... Zero_t variant) verifier.
    """
    p.goal(
        "!x y. (In x y ==> Prov_Q (substitute (substitute "
        "  is_In_internal (numeral x) var_x) "
        "  (numeral y) var_y)) "
        "/\\ (~(In x y) ==> Prov_Q (Not_f (substitute (substitute "
        "  is_In_internal (numeral x) var_x) "
        "  (numeral y) var_y)))"
    )
    p.sorry()


# B1.1 -- Q-encoding of is_substitute_step.
# 13-disjunct Q-formula matching the HOL ``is_substitute_step``. Free
# vars: var_T (trace), var_y (t), var_z (v), var_a (a), var_b (b).
# Composes IS_PAIR_ORD_REPRESENTS + IS_IN_REPRESENTS for the In-checks
# inside each recursive disjunct.
new_constant("is_substitute_step_internal", nat0_ty)
is_substitute_step_internal = mk_const("is_substitute_step_internal", [])


@proof
def IS_SUBSTITUTE_STEP_REPRESENTS(p):
    """|- !T t v a b. is_substitute_step T t v a b ==>
                         Prov_Q (substitute^5 is_substitute_step_internal
                                 (numeral T) var_T
                                 (numeral t) var_y
                                 (numeral v) var_z
                                 (numeral a) var_a
                                 (numeral b) var_b).

    SORRY. Body of is_substitute_step_internal: 13-disjunction mirroring
    is_substitute_step's HOL body (Q_or_chain over the 13 cases), with
    each ``In (Pair_ord _ _) T``-check expressed via IS_PAIR_ORD +
    IS_IN composed inside Q_exists chains for the constructor-witness
    sub-shapes. ~150 lines: 13 disjuncts × (Q-encoded constructor
    pattern) + final assembly via Q_or_chain.

    Proof strategy: case-split on the IS_SUBSTITUTE_STEP_DEF disjunct
    of ``is_substitute_step T t v a b``; in each case dispatch the
    corresponding Q-disjunct's Sigma_1 witness using
    IS_PAIR_ORD_REPRESENTS / IS_IN_REPRESENTS / Q-axiom citations
    over closed numerals.
    """
    p.goal(
        "!T t v a b. is_substitute_step T t v a b ==> "
        "Prov_Q (substitute (substitute (substitute (substitute (substitute "
        "  is_substitute_step_internal "
        "  (numeral T) var_T) "
        "  (numeral t) var_y) "
        "  (numeral v) var_z) "
        "  (numeral a) var_a) "
        "  (numeral b) var_b)"
    )
    p.sorry()


# B1.2 -- Q-encoding of is_substitute_trace.
# Free vars: var_T (trace), var_x (F), var_y (t), var_z (v), var_w (r).
# Body: the conjunction
#   In (Pair_ord var_x var_w) var_T
#   /\ (Forall_f var_a (Forall_f var_b
#         (In (Pair_ord var_a var_b) var_T ==>
#          is_substitute_step_internal[var_T, var_y, var_z, var_a, var_b])))
# at the Q level. The single bound-variable forall is over (var_a, var_b),
# matching the HOL definition's ``!a b. ...``.
new_constant("is_substitute_trace_internal", nat0_ty)
is_substitute_trace_internal = mk_const("is_substitute_trace_internal", [])


@proof
def IS_SUBSTITUTE_TRACE_REPRESENTS(p):
    """|- !T F t v r. is_substitute_trace T F t v r ==>
                         Prov_Q (substitute^5 is_substitute_trace_internal
                                 (numeral T) var_T
                                 (numeral F) var_x
                                 (numeral t) var_y
                                 (numeral v) var_z
                                 (numeral r) var_w).

    SORRY. Combines IS_PAIR_ORD_REPRESENTS (for clause (i): In (Pair_ord
    F r) T) with IS_IN_REPRESENTS and IS_SUBSTITUTE_STEP_REPRESENTS
    (for clause (ii): the bounded forall over members of T). The
    bounded forall is decidable in Q + HF because T is a closed
    numeral with finitely many members witnessed by Q12 (foundation /
    HF nat0_lt). ~100 lines.
    """
    p.goal(
        "!T F t v r. is_substitute_trace T F t v r ==> "
        "Prov_Q (substitute (substitute (substitute (substitute (substitute "
        "  is_substitute_trace_internal "
        "  (numeral T) var_T) "
        "  (numeral F) var_x) "
        "  (numeral t) var_y) "
        "  (numeral v) var_z) "
        "  (numeral r) var_w)"
    )
    p.sorry()


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
# TODO -- discharge via Q + HF (preferred). Prov_Q has been collapsed
# to ``\n. ?p. Proof_Q p n``, so the Q-internal form is the existential
# closure
#   Prov_Q_internal(x) := ?_internal y. Proof_Q_internal(y, x).
# Under the HF strengthening (axioms Q8-Q12, already in q_proof.py):
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
#   * Backward direction (Q proves ==> HOL): Stage 6 HF |= (Q + Q8-Q12)
#     is one HOL theorem citation per axiom.
#
# Side conditions IS_FORM and FREE_IN become routine once
# Prov_Q_internal has its defining body, both decided by the same
# syntactic recursion that verifies is_form for the connectives in
# q_syntax.py (which already covers In_a via IS_FORM_AT_IN).
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
    print("    IS_SUBSTITUTE_STEP_AT  : <13-disjunct body>")
    print("    IS_SUBSTITUTE_TRACE_DEF:", pp_thm(IS_SUBSTITUTE_TRACE_DEF))
    print("    IS_SUBSTITUTE_TRACE_AT :", pp_thm(IS_SUBSTITUTE_TRACE_AT))
    print(
        "    TRACE_STEP_MONO        : |- !T1 T2. (!x. In x T1 ==> In x T2) "
        "==> !t v a b. is_substitute_step T1 ... ==> is_substitute_step T2 ..."
    )
    print(
        "    TRACE_EXISTS (SORRY)   : |- !F t v. (is_term F \\/ is_form F) "
        "==> ?T. is_substitute_trace T F t v (substitute F t v)"
    )
    print(
        "    IS_POW2_REPRESENTS (SORRY)            : |- !x. Prov_Q (.. is_pow2_internal .. (pow2 x) ..)"
    )
    print(
        "    IS_PAIR_ORD_REPRESENTS (SORRY)        : |- !x y. Prov_Q (.. is_Pair_ord_internal .. (Pair_ord x y) ..)"
    )
    print(
        "    IS_IN_REPRESENTS (SORRY)              : |- !x y. (In x y => Prov_Q ..) /\\ (~In x y => Prov_Q (Not_f ..))"
    )
    print(
        "    IS_SUBSTITUTE_STEP_REPRESENTS (SORRY) : |- !T t v a b. is_substitute_step T t v a b => Prov_Q .."
    )
    print(
        "    IS_SUBSTITUTE_TRACE_REPRESENTS (SORRY): |- !T F t v r. is_substitute_trace T F t v r => Prov_Q .."
    )
    print("    SUBSTITUTE_REPRESENTS  :", pp_thm(SUBSTITUTE_REPRESENTS))
    print()
    print("Stage 3D (a) -- representability of provability (SORRY).")
    print("    SUBSTITUTE_2_DEF        :", pp_thm(SUBSTITUTE_2_DEF))
    print("    PROV_Q_REPRESENTS       :", pp_thm(PROV_Q_REPRESENTS))
    print("    IS_FORM_PROV_Q_INTERNAL :", pp_thm(IS_FORM_PROV_Q_INTERNAL))
    print("    FREE_IN_PROV_Q_INTERNAL :", pp_thm(FREE_IN_PROV_Q_INTERNAL))
