"""Naturals with 0: ``nat0`` carved from ``num`` via the trivial subtype.

pyzar's ``num`` is Landau-style (1, 2, 3, ...); the HF/Ackermann
encoding wants a 0. We introduce ``nat0`` as a fresh HOL type
isomorphic to ``num`` via the trivial subtype predicate ``\\n:num. n = n``,
and re-orient the iso so that

    rep_nat0 0      = 1
    rep_nat0 (S n)  = SUC (rep_nat0 n).

That is, ``nat0`` value ``k`` corresponds to ``num`` value ``k + 1``.
With this, every Peano-style fact on ``nat0`` lifts from the
corresponding ``num`` fact through the iso.
"""

from fusion import (
    Var,
    Abs,
    REFL,
    TRANS,
    ASSUME,
    EQ_MP,
    INST,
    HolError,
)
from basics import (
    mk_abs,
    mk_app,
    mk_const,
    mk_eq,
    rand,
)
from tactics import (
    AP_TERM,
    AP_THM,
    BETA_CONV,
    SYM,
    SPEC,
    GEN,
    CONJ,
    CONJUNCT1,
    CONJUNCT2,
    DISCH,
    MP,
    NOT_ELIM,
)
from num import (
    num_ty,
    mk_suc,
    SUC,
    ONE,
    AXIOM_3,
    AXIOM_4,
    INDUCTION,
    NUM_RECURSION,
)
from fusion import aty, INST_TYPE
from parser import (
    define as _define,
    define,
    parse_type,
)
from tactics import unfold_def_at, REWRITE_RULE
from axioms import SELECT_AX, mk_and, mk_forall
from proof import proof, register_induction, InductionStrategy
from data_type import define_basic_subtype


# ---------------------------------------------------------------------------
# Step 1.  Witness for new_basic_type_definition.
#
# Predicate: \n:num. n = n.  Witness:  (\n. n = n) 1, obtained via BETA_CONV
# from REFL 1.
# ---------------------------------------------------------------------------

_n_num = Var("n", num_ty)
_NAT0_PRED = mk_abs(_n_num, mk_eq(_n_num, _n_num))  # \n:num. n = n
_pred_at_one = mk_app(_NAT0_PRED, ONE)  # (\n. n = n) 1
_beta_at_one = BETA_CONV(_pred_at_one)  # |- (\n. n = n) 1 = (1 = 1)
_NAT0_WITNESS = EQ_MP(SYM(_beta_at_one), REFL(ONE))  # |- (\n. n = n) 1


# ---------------------------------------------------------------------------
# Step 2.  Carve out ``nat0`` as a (trivial) subtype of ``num``.
# ---------------------------------------------------------------------------

_NAT0_SUBTYPE = define_basic_subtype("nat0", ("abs_nat0", "rep_nat0"), _NAT0_WITNESS)
ABS_REP_NAT0 = _NAT0_SUBTYPE.abs_rep
REP_ABS_NAT0 = _NAT0_SUBTYPE.rep_abs
# ABS_REP_NAT0 : |- abs_nat0 (rep_nat0 a) = a                          (a : nat0)
# REP_ABS_NAT0 : |- (\n. n = n) r = (rep_nat0 (abs_nat0 r) = r)        (r : num)

nat0_ty = _NAT0_SUBTYPE.ty
abs_nat0 = _NAT0_SUBTYPE.abs_const
rep_nat0 = _NAT0_SUBTYPE.rep_const


# Specialise REP_ABS_NAT0 once: the predicate ``(\n. n = n) r`` reduces to the
# tautology ``r = r``, so we get the unconditional round-trip
#   |- !r:num. rep_nat0 (abs_nat0 r) = r.
def _prove_rep_abs():
    r_var = Var("r", num_ty)
    # REP_ABS_NAT0 : |- (\n. n = n) r = (rep_nat0 (abs_nat0 r) = r).
    pred_eq = REP_ABS_NAT0  # uses the same r as bound by the kernel.
    # The kernel produced REP_ABS_NAT0 with r:num as its free var; reuse that.
    # LHS beta-reduces to (r = r), which is REFL r.
    lhs = pred_eq._concl.fun.arg  # the (\n. n = n) r side
    beta = BETA_CONV(lhs)  # |- (\n. n = n) r = (r = r)
    refl_r = REFL(r_var)  # |- r = r
    # (\n. n = n) r holds, by EQ_MP of SYM(beta) on refl_r.
    pred_holds = EQ_MP(SYM(beta), refl_r)
    # Now apply REP_ABS_NAT0 to extract the round-trip equation.
    rep_abs_eq_r = EQ_MP(pred_eq, pred_holds)  # |- rep_nat0 (abs_nat0 r) = r
    return GEN(r_var, rep_abs_eq_r)


REP_ABS = _prove_rep_abs()  # |- !r. rep_nat0 (abs_nat0 r) = r


# ---------------------------------------------------------------------------
# Step 3.  Define ``0`` and ``SUC0`` on nat0.
#
#   0    := abs_nat0 1
#   SUC0 := \n:nat0. abs_nat0 (SUC (rep_nat0 n))
# ---------------------------------------------------------------------------

ZERO_DEF = define("0", nat0_ty, "abs_nat0 1")
ZERO = mk_const("0", [])

SUC0_DEF = define("SUC0", "nat0 -> nat0", "\\n:nat0. abs_nat0 (SUC (rep_nat0 n))")
SUC0 = mk_const("SUC0", [])


def mk_suc0(t):
    return mk_app(SUC0, t)


# Standard variable names re-used throughout nat0 work.
m = Var("m", nat0_ty)
n = Var("n", nat0_ty)
k = Var("k", nat0_ty)


# ---------------------------------------------------------------------------
# Step 4.  AXIOM_3_0 :  |- !n. ~(SUC0 n = 0).
#
# Strategy: suppose SUC0 n = 0; unfold both sides to abs_nat0 (...) and apply
# rep_nat0 to peel via REP_ABS, leaving SUC (rep_nat0 n) = 1, which AXIOM_3
# refutes.
# ---------------------------------------------------------------------------


@proof
def AXIOM_3_0(p):
    p.goal("!n:nat0. ~(SUC0 n = 0)")
    p.fix("n")
    with p.suppose("h: SUC0 n = 0"):
        # Unfold SUC0 and 0 to expose the underlying abs_nat0 (...) shapes.
        with p.calc("h_abs: abs_nat0 (SUC (rep_nat0 n))") as c:
            c.step("= SUC0 n").by_thm(SYM(p.unfold(SUC0_DEF, "n")))
            c.step("= 0").by_thm(p.fact("h"))
            c.step("= abs_nat0 1").by_thm(ZERO_DEF)
        # Apply rep_nat0 to both sides; both are rep_abs round-trips.
        h_rep = AP_TERM(rep_nat0, p.fact("h_abs"))
        eq_lhs_peel = SPEC(mk_suc(mk_app(rep_nat0, p._parse("n"))), REP_ABS)
        # |- rep_nat0 (abs_nat0 (SUC (rep_nat0 n))) = SUC (rep_nat0 n)
        eq_rhs_peel = SPEC(ONE, REP_ABS)
        # |- rep_nat0 (abs_nat0 1) = 1
        with p.calc("h_peel: SUC (rep_nat0 n)") as c:
            c.step("= rep_nat0 (abs_nat0 (SUC (rep_nat0 n)))").by_thm(SYM(eq_lhs_peel))
            c.step("= rep_nat0 (abs_nat0 1)").by_thm(h_rep)
            c.step("= 1").by_thm(eq_rhs_peel)
        # AXIOM_3 at rep_nat0 n: ~(SUC (rep_nat0 n) = 1).
        neq = SPEC(mk_app(rep_nat0, p._parse("n")), AXIOM_3)
        p.absurd().by_thm(MP(NOT_ELIM(neq), p.fact("h_peel")))


# ---------------------------------------------------------------------------
# Step 5.  AXIOM_4_0 :  |- !m n. SUC0 m = SUC0 n ==> m = n.
#
# Strategy: unfold SUC0; peel both sides via REP_ABS to a num equation;
# apply AXIOM_4 to strip the SUC; apply abs_nat0 + ABS_REP_NAT0 to recover
# the nat0 equation.
# ---------------------------------------------------------------------------


@proof
def AXIOM_4_0(p):
    p.goal("!m n. SUC0 m = SUC0 n ==> m = n", types={"m": nat0_ty, "n": nat0_ty})
    p.fix("m n")
    p.assume("h: SUC0 m = SUC0 n")
    m_t = p._parse("m")
    n_t = p._parse("n")
    rep_m = mk_app(rep_nat0, m_t)
    rep_n = mk_app(rep_nat0, n_t)
    suc_rep_m = mk_suc(rep_m)
    suc_rep_n = mk_suc(rep_n)

    # Unfold SUC0 on both sides of h, then take rep_nat0 of both sides.
    with p.calc("h_abs: abs_nat0 (SUC (rep_nat0 m))") as c:
        c.step("= SUC0 m").by_thm(SYM(p.unfold(SUC0_DEF, "m")))
        c.step("= SUC0 n").by_thm(p.fact("h"))
        c.step("= abs_nat0 (SUC (rep_nat0 n))").by_thm(p.unfold(SUC0_DEF, "n"))
    h_rep = AP_TERM(rep_nat0, p.fact("h_abs"))
    # |- rep_nat0 (abs_nat0 (SUC (rep_nat0 m))) = rep_nat0 (abs_nat0 (SUC (rep_nat0 n)))

    eq_m_peel = SPEC(
        suc_rep_m, REP_ABS
    )  # rep_nat0 (abs_nat0 (SUC (rep_nat0 m))) = SUC (rep_nat0 m)
    eq_n_peel = SPEC(suc_rep_n, REP_ABS)
    with p.calc("h_peel: SUC (rep_nat0 m)") as c:
        c.step("= rep_nat0 (abs_nat0 (SUC (rep_nat0 m)))").by_thm(SYM(eq_m_peel))
        c.step("= rep_nat0 (abs_nat0 (SUC (rep_nat0 n)))").by_thm(h_rep)
        c.step("= SUC (rep_nat0 n)").by_thm(eq_n_peel)
    # AXIOM_4 strips the SUC.
    rep_eq = MP(SPEC(rep_n, SPEC(rep_m, AXIOM_4)), p.fact("h_peel"))
    # |- rep_nat0 m = rep_nat0 n
    p.have("rep_eq:").by_thm(rep_eq)
    # Now apply abs_nat0 to both sides and round-trip via ABS_REP_NAT0.
    abs_app = AP_TERM(abs_nat0, rep_eq)
    # |- abs_nat0 (rep_nat0 m) = abs_nat0 (rep_nat0 n)
    a_var = Var("a", nat0_ty)
    abs_rep_m = INST([(m_t, a_var)], ABS_REP_NAT0)  # |- abs_nat0 (rep_nat0 m) = m
    abs_rep_n = INST([(n_t, a_var)], ABS_REP_NAT0)
    with p.calc("m", thus=True) as c:
        c.step("= abs_nat0 (rep_nat0 m)").by_thm(SYM(abs_rep_m))
        c.step("= abs_nat0 (rep_nat0 n)").by_thm(abs_app)
        c.step("= n").by_thm(abs_rep_n)


# ---------------------------------------------------------------------------
# Step 6.  INDUCT_0 helper -- transports num.py's INDUCT through the iso.
#
# Given:
#     pred = \v:nat0. body[v]   (an Abs)
#     base_th : |- body[v := 0]
#     step_th : |- !v. body[v] ==> body[SUC0 v]
# returns
#     |- !v. body[v].
#
# Strategy: define Q := \k:num. pred (abs_nat0 k); transport base_th and
# step_th to ``Q 1`` and ``!k. Q k ==> Q (SUC k)`` via ZERO_DEF / SUC0_DEF
# and REP_ABS; apply num INDUCTION at Q to get !k. Q k; SPEC at rep_nat0 v
# and peel via ABS_REP_NAT0 to recover body[v].
# ---------------------------------------------------------------------------


def INDUCT_0(pred, base_th, step_th):
    if not isinstance(pred, Abs):
        raise HolError("INDUCT_0: pred must be an Abs")
    v_var = pred.bvar
    if v_var.ty != nat0_ty:
        raise HolError("INDUCT_0: pred's bound variable must have type nat0")

    k_var = Var("k", num_ty)
    abs_k = mk_app(abs_nat0, k_var)
    Q = mk_abs(k_var, mk_app(pred, abs_k))

    # ----- Q 1: transport base_th. -----
    Q_at_1 = mk_app(Q, ONE)
    pred_at_zero = mk_app(pred, ZERO)
    beta_Q_1 = BETA_CONV(Q_at_1)  # |- Q 1 = pred (abs_nat0 1)
    pred_eq_zero = AP_TERM(pred, SYM(ZERO_DEF))  # |- pred (abs_nat0 1) = pred 0
    beta_pred_zero = BETA_CONV(pred_at_zero)  # |- pred 0 = body[v := 0]
    Q_1_eq_body0 = TRANS(TRANS(beta_Q_1, pred_eq_zero), beta_pred_zero)
    Q_1_th = EQ_MP(SYM(Q_1_eq_body0), base_th)  # |- Q 1

    # ----- !k. Q k ==> Q (SUC k): transport step_th. -----
    Q_k = mk_app(Q, k_var)
    Q_sk = mk_app(Q, mk_suc(k_var))
    pred_at_abs_k = mk_app(pred, abs_k)

    # Q k = pred (abs_nat0 k) = body[v := abs_nat0 k]
    beta_Q_k = BETA_CONV(Q_k)
    beta_pred_abs_k = BETA_CONV(pred_at_abs_k)
    Q_k_eq_body_at_abs_k = TRANS(beta_Q_k, beta_pred_abs_k)

    # SUC0 (abs_nat0 k) = abs_nat0 (SUC k):
    #   SUC0 (abs_nat0 k) = (\n. abs_nat0 (SUC (rep_nat0 n))) (abs_nat0 k)  by AP_THM SUC0_DEF
    #                     = abs_nat0 (SUC (rep_nat0 (abs_nat0 k)))           by BETA
    #                     = abs_nat0 (SUC k)                                 by REP_ABS
    SUC0_at_abs_k = AP_THM(SUC0_DEF, abs_k)
    beta_SUC0 = BETA_CONV(rand(SUC0_at_abs_k._concl))
    rep_abs_k_eq = SPEC(k_var, REP_ABS)  # |- rep_nat0 (abs_nat0 k) = k
    fix_via_rep = AP_TERM(abs_nat0, AP_TERM(SUC, rep_abs_k_eq))
    SUC0_abs_k_eq_abs_sk = TRANS(TRANS(SUC0_at_abs_k, beta_SUC0), fix_via_rep)
    # |- SUC0 (abs_nat0 k) = abs_nat0 (SUC k)

    # body[v := SUC0 abs_k] = pred (SUC0 abs_k) = pred (abs_nat0 (SUC k)) = body[v := abs_nat0 (SUC k)]
    pred_at_SUC0_abs_k = mk_app(pred, mk_app(SUC0, abs_k))
    beta_pred_SUC0 = BETA_CONV(pred_at_SUC0_abs_k)
    # Now Q (SUC k) = pred (abs_nat0 (SUC k)) = body[v := abs_nat0 (SUC k)] = pred (SUC0 abs_k) = body[v := SUC0 abs_k]
    beta_Q_sk = BETA_CONV(Q_sk)
    pred_eq_via_SUC0 = AP_TERM(pred, SYM(SUC0_abs_k_eq_abs_sk))
    # |- pred (abs_nat0 (SUC k)) = pred (SUC0 (abs_nat0 k))
    Q_sk_eq_body_at_SUC0_abs_k = TRANS(
        TRANS(beta_Q_sk, pred_eq_via_SUC0), beta_pred_SUC0
    )

    # step_th @ abs_k : body[v := abs_k] ==> body[v := SUC0 abs_k]
    step_inst = SPEC(abs_k, step_th)
    Qk_assume = ASSUME(Q_k)
    body_at_abs_k = EQ_MP(Q_k_eq_body_at_abs_k, Qk_assume)
    body_at_SUC0_abs_k = MP(step_inst, body_at_abs_k)
    Qsk_th = EQ_MP(SYM(Q_sk_eq_body_at_SUC0_abs_k), body_at_SUC0_abs_k)
    Qstep = GEN(k_var, DISCH(Q_k, Qsk_th))

    # ----- num INDUCTION at Q: !k. Q k. -----
    ind_at_Q = SPEC(Q, INDUCTION)
    Q_all = MP(ind_at_Q, CONJ(Q_1_th, Qstep))  # |- !k. Q k

    # ----- Recover body[v] for arbitrary v:nat0. -----
    rep_v = mk_app(rep_nat0, v_var)
    Q_at_rep = SPEC(rep_v, Q_all)  # |- Q (rep_nat0 v)
    beta_Q_rep = BETA_CONV(
        mk_app(Q, rep_v)
    )  # |- Q (rep_nat0 v) = pred (abs_nat0 (rep_nat0 v))
    a_var = Var("a", nat0_ty)
    abs_rep_at_v = INST([(v_var, a_var)], ABS_REP_NAT0)  # |- abs_nat0 (rep_nat0 v) = v
    pred_eq_at_v = AP_TERM(
        pred, abs_rep_at_v
    )  # |- pred (abs_nat0 (rep_nat0 v)) = pred v
    beta_pred_v = BETA_CONV(mk_app(pred, v_var))  # |- pred v = body[v := v]
    Q_rep_eq_body_v = TRANS(TRANS(beta_Q_rep, pred_eq_at_v), beta_pred_v)
    body_at_v = EQ_MP(Q_rep_eq_body_v, Q_at_rep)
    return GEN(v_var, body_at_v)


# ---------------------------------------------------------------------------
# INDUCTION_0 :  |- !P. P 0 /\ (!n. P n ==> P (SUC0 n)) ==> !n. P n.
# Direct application of INDUCT_0 to a generic predicate variable P.
# ---------------------------------------------------------------------------

_P_nat0_ty = parse_type("nat0 -> bool")


def _prove_induction_0_thm():
    from axioms import mk_forall, mk_imp, mk_and

    P_var = Var("P", _P_nat0_ty)
    n_var = Var("n", nat0_ty)
    body_at_n = mk_app(P_var, n_var)  # P n
    body_at_0 = mk_app(P_var, ZERO)  # P 0
    body_at_Sn = mk_app(P_var, mk_suc0(n_var))  # P (SUC0 n)
    step_term = mk_forall(n_var, mk_imp(body_at_n, body_at_Sn))

    pred = mk_abs(n_var, body_at_n)  # \n. P n
    h_base = ASSUME(body_at_0)
    h_step = ASSUME(step_term)
    forall_th = INDUCT_0(pred, h_base, h_step)  # |- !n. P n  (with both ASSUMEs)

    # Re-package both hypotheses as a single conjunction antecedent.
    AB = mk_and(body_at_0, step_term)
    AB_assume = ASSUME(AB)
    forall_via_conj = MP(
        MP(
            DISCH(body_at_0, DISCH(step_term, forall_th)),
            CONJUNCT1(AB_assume),
        ),
        CONJUNCT2(AB_assume),
    )
    impl = DISCH(AB, forall_via_conj)
    return GEN(P_var, impl)


INDUCTION_0 = _prove_induction_0_thm()


# ---------------------------------------------------------------------------
# INDUCT_PROVE_0 -- high-level induction template for nat0 (mirrors
# num.py's ``INDUCT_PROVE``). Used both directly and as the ``induct_prove``
# callback of the InductionStrategy registration below.
# ---------------------------------------------------------------------------


def INDUCT_PROVE_0(var, body, base, step_fn):
    pred = mk_abs(var, body)
    IH = ASSUME(body)
    step_inner = step_fn(IH)
    step = GEN(var, DISCH(body, step_inner))
    return INDUCT_0(pred, base, step)


# Teach ``p.induction("n")`` how to handle a nat0 variable.
register_induction(
    InductionStrategy(
        ty=nat0_ty,
        base_term=ZERO,
        succ_fn=mk_suc0,
        induct_prove=INDUCT_PROVE_0,
    )
)


# ---------------------------------------------------------------------------
# Step 7.  NUM_RECURSION_0 :  |- !c h. ?fn:nat0->A. fn 0 = c /\ !n. fn (SUC0 n) = h n (fn n).
#
# Strategy: lift NUM_RECURSION from num via the iso. Given c:A and
# h:nat0->A->A, build h':num->A->A by h' k a := h (abs_nat0 k) a; apply
# NUM_RECURSION at (c, h') to get gn:num->A with gn 1 = c and
# gn (SUC k) = h (abs_nat0 k) (gn k); set fn := \n. gn (rep_nat0 n) and
# verify both recursion equations via REP_ABS / ABS_REP_NAT0.
# ---------------------------------------------------------------------------

from tactics import EXISTS, CHOOSE_WITNESS, AP_TERM as _AP_TERM, GENL  # noqa: E402 -- imported lazily for the recursion lift below


def _prove_num_recursion_0():
    from axioms import mk_forall, mk_and

    # Type variable A and the relevant function types.
    A = aty
    nat0_to_A = parse_type("nat0 -> A")
    num_to_A = parse_type("num -> A")
    h_nat0 = parse_type("nat0 -> A -> A")

    c_var = Var("c", A)
    h_var = Var("h", h_nat0)
    fn_var = Var("fn", nat0_to_A)
    n_var = Var("n", nat0_ty)
    k_var = Var("k", num_ty)
    a_var = Var("a", A)

    # h' : num -> A -> A, h' = \k a. h (abs_nat0 k) a.
    h_prime = mk_abs(
        k_var,
        mk_abs(
            a_var,
            mk_app(h_var, mk_app(abs_nat0, k_var), a_var),
        ),
    )

    # NUM_RECURSION at A specialised at (c, h'):
    # |- ?gn:num->A. gn 1 = c /\ !k. gn (SUC k) = h' k (gn k)
    NR = INST_TYPE([(A, aty)], NUM_RECURSION)  # already at A; no-op
    NR_at_ch = SPEC(h_prime, SPEC(c_var, NR))

    # CHOOSE the witness gn (still under hypothesis on existential).
    pred_gn = NR_at_ch._concl.arg  # the (\gn. ...) predicate
    gn_props = CHOOSE_WITNESS(pred_gn, NR_at_ch)
    # gn_props : |- (sel) 1 = c /\ !k. (sel) (SUC k) = h' k ((sel) k)
    # where (sel) = @gn. ... ; we'll call it gn_term.
    sel_const = mk_const("@", [(num_to_A, aty)])
    gn_term = mk_app(sel_const, pred_gn)
    g_base = CONJUNCT1(gn_props)  # |- gn_term 1 = c
    g_step = CONJUNCT2(gn_props)  # |- !k. gn_term (SUC k) = h' k (gn_term k)

    # fn := \n:nat0. gn_term (rep_nat0 n).
    fn_body = mk_abs(n_var, mk_app(gn_term, mk_app(rep_nat0, n_var)))

    # ----- Prove fn 0 = c. -----
    # fn 0 = (\n. gn_term (rep_nat0 n)) 0 = gn_term (rep_nat0 0)
    fn_at_0 = mk_app(fn_body, ZERO)
    beta_fn0 = BETA_CONV(fn_at_0)  # |- fn 0 = gn_term (rep_nat0 0)
    # rep_nat0 0 = rep_nat0 (abs_nat0 1) = 1 (by REP_ABS at 1, plus ZERO_DEF)
    rep0_eq = TRANS(_AP_TERM(rep_nat0, ZERO_DEF), SPEC(ONE, REP_ABS))
    # rep0_eq : |- rep_nat0 0 = 1
    gn_at_rep0 = _AP_TERM(gn_term, rep0_eq)  # |- gn_term (rep_nat0 0) = gn_term 1
    fn0_eq_c = TRANS(TRANS(beta_fn0, gn_at_rep0), g_base)  # |- fn 0 = c

    # ----- Prove !n. fn (SUC0 n) = h n (fn n). -----
    fn_at_n = mk_app(fn_body, n_var)
    beta_fn_n = BETA_CONV(fn_at_n)  # |- fn n = gn_term (rep_nat0 n)
    fn_at_Sn = mk_app(fn_body, mk_suc0(n_var))
    beta_fn_Sn = BETA_CONV(fn_at_Sn)  # |- fn (SUC0 n) = gn_term (rep_nat0 (SUC0 n))

    # rep_nat0 (SUC0 n) = SUC (rep_nat0 n):
    #   SUC0 n = (\n. abs_nat0 (SUC (rep_nat0 n))) n   by AP_THM SUC0_DEF n
    #          = abs_nat0 (SUC (rep_nat0 n))            by BETA
    #   rep_nat0 (SUC0 n) = rep_nat0 (abs_nat0 (SUC (rep_nat0 n))) = SUC (rep_nat0 n)  by REP_ABS
    SUC0_at_n = AP_THM(SUC0_DEF, n_var)
    beta_SUC0_n = BETA_CONV(rand(SUC0_at_n._concl))
    SUC0_unfold = TRANS(
        SUC0_at_n, beta_SUC0_n
    )  # |- SUC0 n = abs_nat0 (SUC (rep_nat0 n))
    rep_SUC0 = _AP_TERM(rep_nat0, SUC0_unfold)
    rep_abs_chain = SPEC(mk_suc(mk_app(rep_nat0, n_var)), REP_ABS)
    rep_SUC0_n_eq = TRANS(rep_SUC0, rep_abs_chain)
    # |- rep_nat0 (SUC0 n) = SUC (rep_nat0 n)

    # gn_term (rep_nat0 (SUC0 n)) = gn_term (SUC (rep_nat0 n))
    gn_at_repSn = _AP_TERM(gn_term, rep_SUC0_n_eq)
    # gn_term (SUC (rep_nat0 n)) = h' (rep_nat0 n) (gn_term (rep_nat0 n))   via g_step
    g_step_at = SPEC(mk_app(rep_nat0, n_var), g_step)
    # h' (rep_nat0 n) (gn_term (rep_nat0 n)) = (\k a. h (abs_nat0 k) a) (rep_nat0 n) (gn_term (rep_nat0 n))
    # Beta-reduce twice.
    h_prime_at_rep = mk_app(h_prime, mk_app(rep_nat0, n_var))
    beta_h_prime_1 = BETA_CONV(h_prime_at_rep)
    # |- (\k a. h (abs_nat0 k) a) (rep_nat0 n) = \a. h (abs_nat0 (rep_nat0 n)) a
    inner = AP_THM(beta_h_prime_1, mk_app(gn_term, mk_app(rep_nat0, n_var)))
    beta_h_prime_2 = BETA_CONV(rand(inner._concl))
    # |- (\a. h (abs_nat0 (rep_nat0 n)) a) (gn_term (rep_nat0 n))
    #     = h (abs_nat0 (rep_nat0 n)) (gn_term (rep_nat0 n))
    h_prime_eval = TRANS(inner, beta_h_prime_2)
    # |- h' (rep_nat0 n) (gn_term (rep_nat0 n)) = h (abs_nat0 (rep_nat0 n)) (gn_term (rep_nat0 n))

    # abs_nat0 (rep_nat0 n) = n  by ABS_REP_NAT0 (free var a; INST to n_var)
    abs_rep_n = INST([(n_var, Var("a", nat0_ty))], ABS_REP_NAT0)
    # h (abs_nat0 (rep_nat0 n)) (...) = h n (...)
    h_arg_fix = AP_THM(
        _AP_TERM(h_var, abs_rep_n), mk_app(gn_term, mk_app(rep_nat0, n_var))
    )

    # Compose: fn (SUC0 n)
    #   = gn_term (rep_nat0 (SUC0 n))                         beta_fn_Sn
    #   = gn_term (SUC (rep_nat0 n))                          gn_at_repSn
    #   = h' (rep_nat0 n) (gn_term (rep_nat0 n))              g_step_at
    #   = h (abs_nat0 (rep_nat0 n)) (gn_term (rep_nat0 n))    h_prime_eval
    #   = h n (gn_term (rep_nat0 n))                          h_arg_fix
    #   = h n (fn n)                                           SYM beta_fn_n + AP_TERM
    h_n_fn_n = _AP_TERM(mk_app(h_var, n_var), SYM(beta_fn_n))
    # |- h n (gn_term (rep_nat0 n)) = h n (fn n)

    fn_Sn_eq = TRANS(
        TRANS(
            TRANS(
                TRANS(TRANS(beta_fn_Sn, gn_at_repSn), g_step_at),
                h_prime_eval,
            ),
            h_arg_fix,
        ),
        h_n_fn_n,
    )
    # |- fn (SUC0 n) = h n (fn n)
    fn_Sn_forall = GEN(n_var, fn_Sn_eq)

    # Combine and witness.
    combined = CONJ(fn0_eq_c, fn_Sn_forall)
    # Witness fn for the existential.
    # ?fn:nat0->A. fn 0 = c /\ !n. fn (SUC0 n) = h n (fn n)
    pred = mk_abs(
        fn_var,
        mk_and(
            mk_eq(mk_app(fn_var, ZERO), c_var),
            mk_forall(
                n_var,
                mk_eq(
                    mk_app(fn_var, mk_suc0(n_var)),
                    mk_app(mk_app(h_var, n_var), mk_app(fn_var, n_var)),
                ),
            ),
        ),
    )
    exist_th = EXISTS(pred, fn_body, combined)
    return GENL([c_var, h_var], exist_th)


NUM_RECURSION_0 = _prove_num_recursion_0()


# ---------------------------------------------------------------------------
# Step 8.  define_recursive_0 -- declare a binary operator on nat0 by
# primitive recursion on the second argument starting at 0.
#
# Given:
#     fn_ty       -- HOL type of the operator (e.g. nat0 -> nat0 -> A)
#     x_var       -- carried (non-recursive) parameter
#     result_ty   -- the type A of the operator's value
#     c           -- term of type result_ty (value at recursion var = 0)
#     h           -- Abs(k:nat0, Abs(a:result_ty, body[k, a, x_var]))
# Return:
#     BASE : |- !x. name x 0 = c
#     STEP : |- !x y. name x (SUC0 y) = body[k:=y, a:=name x y].
#
# Mirrors num.py's define_recursive but at base 0 / SUC0, and uses
# NUM_RECURSION_0 instead of NUM_RECURSION.
# ---------------------------------------------------------------------------


def define_recursive_0(name, fn_ty, x_var, c, h, *, result_ty, infix=None):
    if not isinstance(h, Abs) or not isinstance(h.body, Abs):
        raise HolError("define_recursive_0: h must be Abs(k, Abs(a, body))")

    from fusion import Tyapp

    fn_ty_inner = Tyapp("fun", (nat0_ty, result_ty))  # nat0 -> result_ty
    fn_var = Var("fn", fn_ty_inner)
    n_var = Var("n", nat0_ty)
    y_var = Var("y", nat0_ty)

    fn_0 = mk_app(fn_var, ZERO)
    fn_n = mk_app(fn_var, n_var)
    fn_sn = mk_app(fn_var, mk_suc0(n_var))

    # Beta-reduce h n (fn n) once to get the clean step body.
    h_at_n = BETA_CONV(mk_app(h, n_var))  # |- h n = (\a. body[k:=n])
    inner = AP_THM(h_at_n, fn_n)
    full = BETA_CONV(rand(inner._concl))
    h_red = TRANS(inner, full)  # |- h n (fn n) = clean_step
    step_clean = rand(h_red._concl)

    # Clean predicate \fn. fn 0 = c /\ !n. fn (SUC0 n) = clean_step.
    pred_clean = mk_abs(
        fn_var,
        mk_and(mk_eq(fn_0, c), mk_forall(n_var, mk_eq(fn_sn, step_clean))),
    )

    sel_const = mk_const("@", [(fn_ty_inner, aty)])
    sel_at_pc = mk_app(sel_const, pred_clean)  # @fn. pred_clean fn

    # Operator definition: \x y. (@fn. pred_clean fn) y.
    op_rhs = mk_abs(x_var, mk_abs(y_var, mk_app(sel_at_pc, y_var)))
    OP_DEF = _define(name, fn_ty, op_rhs, infix=infix)

    # NUM_RECURSION_0 specialised at this c, h.
    NR_at_A = INST_TYPE([(result_ty, aty)], NUM_RECURSION_0)
    spec_ch = SPEC(h, SPEC(c, NR_at_A))
    pred_raw = spec_ch._concl.arg
    sel_at_raw = mk_app(sel_const, pred_raw)

    body_raw = CHOOSE_WITNESS(pred_raw, spec_ch)
    raw_base = CONJUNCT1(body_raw)  # |- sel_at_raw 0 = c
    raw_step = CONJUNCT2(body_raw)  # |- !n. sel_at_raw (SUC0 n) = h n (sel_at_raw n)

    raw_at_n = SPEC(n_var, raw_step)
    h_red_w = INST([(sel_at_raw, fn_var)], h_red)
    clean_at_n = TRANS(raw_at_n, h_red_w)
    clean_step_forall = GEN(n_var, clean_at_n)

    pc_at_raw_body = CONJ(raw_base, clean_step_forall)
    pc_at_raw_eq = BETA_CONV(mk_app(pred_clean, sel_at_raw))
    pc_at_raw = EQ_MP(SYM(pc_at_raw_eq), pc_at_raw_body)

    sel_inst = INST_TYPE([(fn_ty_inner, aty)], SELECT_AX)
    sel_imp = SPEC(sel_at_raw, SPEC(pred_clean, sel_inst))
    pc_at_sel = MP(sel_imp, pc_at_raw)
    pc_at_sel_eq = BETA_CONV(mk_app(pred_clean, sel_at_pc))
    pc_at_sel_body = EQ_MP(pc_at_sel_eq, pc_at_sel)
    sel_base = CONJUNCT1(pc_at_sel_body)
    sel_step = CONJUNCT2(pc_at_sel_body)

    op_at_x = unfold_def_at(OP_DEF, x_var)

    op_at_x_at_0 = unfold_def_at(op_at_x, ZERO)
    BASE_THM = GEN(x_var, TRANS(op_at_x_at_0, sel_base))

    op_at_x_at_y = unfold_def_at(op_at_x, y_var)
    op_at_x_at_sy = unfold_def_at(op_at_x, mk_suc0(y_var))
    sel_at_sy = SPEC(y_var, sel_step)
    raw_step_eq = TRANS(op_at_x_at_sy, sel_at_sy)
    step_eq = REWRITE_RULE([SYM(op_at_x_at_y)], raw_step_eq)
    STEP_THM = GENL([x_var, y_var], step_eq)

    return BASE_THM, STEP_THM


# ---------------------------------------------------------------------------
# define_unary_0 -- shorter form for unary operators on nat0.
#
# Given:
#     name      -- new constant
#     fn_ty     -- HOL type, must be nat0 -> result_ty
#     c         -- term of type result_ty (value at 0)
#     h         -- Abs(k:nat0, Abs(a:result_ty, body[k, a]))
# Return:
#     BASE : |- name 0 = c
#     STEP : |- !n. name (SUC0 n) = body[k:=n, a:=name n].
#
# Implemented as a thin wrapper over define_recursive_0 with a dummy
# carried parameter, then ``SPEC``ed away.
# ---------------------------------------------------------------------------


def define_unary_0(name, fn_ty, c, h, *, result_ty, infix=None):
    if not isinstance(h, Abs) or not isinstance(h.body, Abs):
        raise HolError("define_unary_0: h must be Abs(k, Abs(a, body))")

    fn_var = Var("fn", fn_ty)
    n_var = Var("n", nat0_ty)

    fn_0 = mk_app(fn_var, ZERO)
    fn_n = mk_app(fn_var, n_var)
    fn_sn = mk_app(fn_var, mk_suc0(n_var))

    h_at_n = BETA_CONV(mk_app(h, n_var))
    inner = AP_THM(h_at_n, fn_n)
    full = BETA_CONV(rand(inner._concl))
    h_red = TRANS(inner, full)
    step_clean = rand(h_red._concl)

    pred_clean = mk_abs(
        fn_var,
        mk_and(mk_eq(fn_0, c), mk_forall(n_var, mk_eq(fn_sn, step_clean))),
    )
    sel_const = mk_const("@", [(fn_ty, aty)])
    sel_at_pc = mk_app(sel_const, pred_clean)

    OP_DEF = _define(name, fn_ty, sel_at_pc, infix=infix)

    NR_at_A = INST_TYPE([(result_ty, aty)], NUM_RECURSION_0)
    spec_ch = SPEC(h, SPEC(c, NR_at_A))
    pred_raw = spec_ch._concl.arg
    sel_at_raw = mk_app(sel_const, pred_raw)

    body_raw = CHOOSE_WITNESS(pred_raw, spec_ch)
    raw_base = CONJUNCT1(body_raw)
    raw_step = CONJUNCT2(body_raw)

    raw_at_n = SPEC(n_var, raw_step)
    h_red_w = INST([(sel_at_raw, fn_var)], h_red)
    clean_at_n = TRANS(raw_at_n, h_red_w)
    clean_step_forall = GEN(n_var, clean_at_n)

    pc_at_raw_body = CONJ(raw_base, clean_step_forall)
    pc_at_raw_eq = BETA_CONV(mk_app(pred_clean, sel_at_raw))
    pc_at_raw = EQ_MP(SYM(pc_at_raw_eq), pc_at_raw_body)

    sel_inst = INST_TYPE([(fn_ty, aty)], SELECT_AX)
    sel_imp = SPEC(sel_at_raw, SPEC(pred_clean, sel_inst))
    pc_at_sel = MP(sel_imp, pc_at_raw)
    pc_at_sel_eq = BETA_CONV(mk_app(pred_clean, sel_at_pc))
    pc_at_sel_body = EQ_MP(pc_at_sel_eq, pc_at_sel)
    sel_base = CONJUNCT1(pc_at_sel_body)  # |- (@pred_clean) 0 = c
    sel_step = CONJUNCT2(pc_at_sel_body)  # |- !n. (@pred_clean) (SUC0 n) = step_clean

    # Connect the operator to the SELECT term.
    op_at_0 = AP_THM(OP_DEF, ZERO)  # |- name 0 = sel_at_pc 0
    BASE_THM = TRANS(op_at_0, sel_base)  # |- name 0 = c

    op_at_sn = AP_THM(OP_DEF, mk_suc0(n_var))  # |- name (SUC0 n) = sel_at_pc (SUC0 n)
    sel_at_sn = SPEC(n_var, sel_step)  # |- sel_at_pc (SUC0 n) = step_clean
    raw_step_eq = TRANS(op_at_sn, sel_at_sn)
    # Rewrite sel_at_pc → name in step_clean's RHS.
    step_eq = REWRITE_RULE([SYM(OP_DEF)], raw_step_eq)
    STEP_THM = GEN(n_var, step_eq)

    return BASE_THM, STEP_THM


# ---------------------------------------------------------------------------
# Self-test: every claimed theorem is printed so a clean run prints clean.
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    from parser import pp_thm

    print("Step 1 OK -- nat0 type carved out of num.")
    print("  ABS_REP_NAT0 :", pp_thm(ABS_REP_NAT0))
    print("  REP_ABS_NAT0 :", pp_thm(REP_ABS_NAT0))
    print("  REP_ABS      :", pp_thm(REP_ABS))
    print("Step 2 OK -- 0 and SUC0 defined.")
    print("  ZERO_DEF     :", pp_thm(ZERO_DEF))
    print("  SUC0_DEF     :", pp_thm(SUC0_DEF))
    print("Step 3 OK -- AXIOM_3_0 proved.")
    print("  AXIOM_3_0    :", pp_thm(AXIOM_3_0))
    print("Step 4 OK -- AXIOM_4_0 proved.")
    print("  AXIOM_4_0    :", pp_thm(AXIOM_4_0))
    print("Step 5 OK -- INDUCTION_0 proved.")
    print("  INDUCTION_0  :", pp_thm(INDUCTION_0))
    print("Step 6 OK -- NUM_RECURSION_0 proved.")
    print("  NUM_RECURSION_0:", pp_thm(NUM_RECURSION_0))
    print("Step 7 OK -- define_recursive_0 / define_unary_0 helpers exported.")
