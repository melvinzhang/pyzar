"""Classical logic theorems built on top of the declarative proof DSL.

Sits above ``proof.py`` so the proofs here can use ``@proof`` blocks; sits
below ``num.py`` so the Peano construction can consume the classical
helpers it needs (``NOT_FORALL_TO_EX_NOT``, ``NOT_EX_TO_FORALL_NOT``).

Provides:

  * ``F_NEQ_T``               |- ~(F = T)
  * ``EXCLUDED_MIDDLE``       |- !t:bool. t \\/ ~t   (Diaconescu)
  * ``NOT_NOT_ELIM``          |- ~~p  =>  |- p
  * ``NOT_EX_TO_FORALL_NOT``  |- ~(?v. body)  =>  |- !v. ~body
  * ``NOT_FORALL_TO_EX_NOT``  |- ~(!v. body)  =>  |- ?v. ~body   (classical)
  * ``COND``                  if-then-else (polymorphic, SELECT-defined)
  * ``COND_T`` / ``COND_F``   |- COND T x y = x ; |- COND F x y = y
"""

from fusion import (
    Var,
    bool_ty,
    aty,
    mk_comb,
    REFL,
    TRANS,
    ASSUME,
    EQ_MP,
    INST_TYPE,
)
from basics import mk_abs, mk_app, mk_const, mk_eq, rand, rator
from axioms import T, F, SELECT_AX, mk_not, mk_or, mk_and, mk_imp
from parser import parse_type, define
from tactics import (
    AP_TERM,
    BETA_CONV,
    BETA_RULE,
    SYM,
    TRUTH,
    EQT_INTRO,
    SPEC,
    GEN,
    GENL,
    CONJ,
    CONJUNCT1,
    CONJUNCT2,
    DISCH,
    MP,
    NOT_ELIM,
    DISJ2,
    FUN_EXT,
    CONTR,
    _select_const,
)
from proof import proof


# Polymorphic predicate type ``A -> bool`` used by the quantifier-negation
# universal forms below.  ``aty`` is the kernel's stock tyvar ``A``; declarative
# proofs that need polymorphism pass it via ``types={"A": aty, ...}``.
_pred_ty = parse_type("A -> bool")


# ---------------------------------------------------------------------------
# F != T  (i.e. |- ~(F = T)).
# ---------------------------------------------------------------------------


@proof
def F_NEQ_T(p):
    p.goal("~(F = T)")
    with p.suppose("h: F = T"):
        p.absurd().by_thm(EQ_MP(SYM(p.fact("h")), TRUTH))


# ---------------------------------------------------------------------------
# EXCLUDED_MIDDLE   |- !t:bool. t \/ ~t.   (Diaconescu's argument.)
#
# Fix t.  Define
#     U = \x:bool. (x = F) \/ t
#     V = \x:bool. (x = T) \/ t.
# Both are inhabited (U F, V T), so SELECT_AX gives
#     (@U = F) \/ t   and   (@V = T) \/ t.
# Case-split: either disjunction yielding t closes immediately.  Otherwise
# @U = F and @V = T.  Suppose t held; then U = (\x.T) = V pointwise, so
# by FUN_EXT @U = @V, hence F = T -- contradicting F_NEQ_T.
# ---------------------------------------------------------------------------


def _pointwise_eq_T(F_lambda, x_var, body, h_t, lam_T):
    lhs_disj = rand(rator(body))
    body_th = DISJ2(lhs_disj, h_t)
    Fx = mk_comb(F_lambda, x_var)
    Fx_eq_body = BETA_CONV(Fx)
    body_eq_T = EQT_INTRO(body_th)
    Fx_eq_T = TRANS(Fx_eq_body, body_eq_T)
    lamT_x = mk_comb(lam_T, x_var)
    T_eq_lamTx = SYM(BETA_CONV(lamT_x))
    return GEN(x_var, TRANS(Fx_eq_T, T_eq_lamTx))


def _diaconescu_F_eq_T(t_var, eq_uF, eq_vT, h_t):
    """Cross-case kernel sub-proof: from {@U=F, @V=T, t} derive F = T."""
    x_var = Var("x", bool_ty)
    U_body = mk_or(mk_eq(x_var, F), t_var)
    V_body = mk_or(mk_eq(x_var, T), t_var)
    U = mk_abs(x_var, U_body)
    V = mk_abs(x_var, V_body)
    select_b = _select_const(bool_ty)
    lam_T = mk_abs(x_var, T)
    U_eq_lamT = FUN_EXT(_pointwise_eq_T(U, x_var, U_body, h_t, lam_T))
    V_eq_lamT = FUN_EXT(_pointwise_eq_T(V, x_var, V_body, h_t, lam_T))
    selU_eq_selV = AP_TERM(select_b, TRANS(U_eq_lamT, SYM(V_eq_lamT)))
    return TRANS(TRANS(SYM(eq_uF), selU_eq_selV), eq_vT)


_SELECT_AX_BOOL = INST_TYPE([(bool_ty, aty)], SELECT_AX)
_t_bool = Var("t", bool_ty)


@proof
def EXCLUDED_MIDDLE(p):
    p.goal("!t:bool. t \\/ ~t")
    p.fix("t")
    p.let("U(x:bool) := (x = F) \\/ t")
    p.let("V(x:bool) := (x = T) \\/ t")

    p.have("U_F: U F").by_disj(REFL(F))
    p.have("V_T: V T").by_disj(REFL(T))

    # ``by`` with the lazy carriers produces ``|- U (@ U)`` /
    # ``|- V (@ V)`` (folded). The downstream cases_on and the
    # _diaconescu_F_eq_T helper expect the unfolded ``@x. body`` shape,
    # so build the SPEC/MP chain by hand and materialize the carrier
    # (substitute ``U := \x. body`` and BETA-normalize) before binding.
    _U_lz = p._lookup_lazy_let("U")
    _V_lz = p._lookup_lazy_let("V")
    _U_at_F = MP(
        SPEC(F, SPEC(_U_lz.carrier, _SELECT_AX_BOOL)), p.fact("U_F")
    )  # |- U (@ U)
    _V_at_T = MP(
        SPEC(T, SPEC(_V_lz.carrier, _SELECT_AX_BOOL)), p.fact("V_T")
    )  # |- V (@ V)
    p.have("U_or: ((@x:bool. (x = F) \\/ t) = F) \\/ t").by_thm(
        p.materialize_let(_U_at_F, "U")
    )
    p.have("V_or: ((@x:bool. (x = T) \\/ t) = T) \\/ t").by_thm(
        p.materialize_let(_V_at_T, "V")
    )

    with p.cases_on("U_or"):
        with p.case("eq_uF: (@x:bool. (x = F) \\/ t) = F"):
            with p.cases_on("V_or"):
                with p.case("eq_vT: (@x:bool. (x = T) \\/ t) = T"):
                    with p.have("nott: ~t").proof():
                        with p.suppose("ht: t"):
                            F_eq_T = _diaconescu_F_eq_T(
                                _t_bool, p.fact("eq_uF"), p.fact("eq_vT"), p.fact("ht")
                            )
                            p.absurd().by_thm(MP(NOT_ELIM(F_NEQ_T), F_eq_T))
                    p.thus("t \\/ ~t").by_disj("nott")
                with p.case("ht: t"):
                    p.thus("t \\/ ~t").by_disj("ht")
        with p.case("ht: t"):
            p.thus("t \\/ ~t").by_disj("ht")


# ---------------------------------------------------------------------------
# Classical helpers built on EM.
# ---------------------------------------------------------------------------


@proof
def NOT_NOT_ELIM_AX(p):
    p.goal("!q:bool. ~~q ==> q")
    p.fix("q")
    p.assume("hnn: ~~q")
    with p.cases_on(EXCLUDED_MIDDLE, "q"):
        with p.case("hq: q"):
            p.thus("q").by_thm(p.fact("hq"))
        with p.case("hnq: ~q"):
            p.absurd().by_conj("hnq", "hnn")


def NOT_NOT_ELIM(th):
    """|- ~~p   =>   |- p"""
    p_t = rand(rand(th._concl))
    return MP(SPEC(p_t, NOT_NOT_ELIM_AX), th)


# Rewrite-friendly form: |- !q. ~~q = q.  Used by ``by_rewrite`` to
# normalise nested negations during arithmetic-on-bool reasoning.
@proof
def NOT_NOT_EQ(p):
    p.goal("!q:bool. ~~q = q")
    p.fix("q")
    p.have("fwd: ~~q ==> q").by_thm(SPEC(Var("q", bool_ty), NOT_NOT_ELIM_AX))
    with p.have("rev: q ==> ~~q").proof():
        p.assume("hq: q")
        with p.suppose("hnq: ~q"):
            p.absurd().by_conj("hnq", "hq")
    p.thus("~~q = q").by_iff("fwd", "rev")


# ---------------------------------------------------------------------------
# Polymorphic universal forms of the quantifier-negation rules.  Each takes a
# generic predicate ``p : A -> bool`` and discharges a quantifier flip.  Call
# sites use the thin Python wrappers below: ``SPEC`` at the concrete predicate,
# ``BETA_RULE`` to normalise the (\\v. body) v redex, then ``MP``.
# ---------------------------------------------------------------------------


@proof
def NOT_EX_TO_FORALL_NOT_AX(prf):
    prf.goal("!p. ~(?v:A. p v) ==> !v:A. ~(p v)", types={"p": _pred_ty, "A": aty})
    prf.fix("p")
    prf.assume("hne: ~(?v:A. p v)")
    with prf.thus("!v:A. ~(p v)").proof():
        prf.fix("v")
        with prf.suppose("hpv: p v"):
            prf.have("hex: ?v:A. p v").by_witness("v", "hpv")
            prf.absurd().by_conj("hne", "hex")


@proof
def NOT_FORALL_TO_EX_NOT_AX(prf):
    prf.goal("!p. ~(!v:A. p v) ==> ?v:A. ~(p v)", types={"p": _pred_ty, "A": aty})
    prf.fix("p")
    prf.assume("hnf: ~(!v:A. p v)")
    with prf.thus("?v:A. ~(p v)").proof():
        with prf.cases_on(EXCLUDED_MIDDLE, "?v:A. ~(p v)"):
            with prf.case("hex: ?v:A. ~(p v)"):
                prf.thus("?v:A. ~(p v)").by_thm(prf.fact("hex"))
            with prf.case("hne: ~(?v:A. ~(p v))"):
                with prf.have("hall: !v:A. p v").proof():
                    prf.fix("v")
                    with prf.have("nn: ~~(p v)").proof():
                        with prf.suppose("hnpv: ~(p v)"):
                            prf.have("hex_neg: ?v:A. ~(p v)").by_witness("v", "hnpv")
                            prf.absurd().by_conj("hne", "hex_neg")
                    prf.thus("p v").by_thm(NOT_NOT_ELIM(prf.fact("nn")))
                prf.absurd().by_conj("hnf", "hall")


def _spec_quant_ax(ax, pred):
    """Common scaffold: ``INST_TYPE`` ``ax`` to the predicate's tyvar, ``SPEC``
    at ``pred``, ``BETA_RULE`` away the resulting (\\v. body) v redex."""
    v_ty = pred.bvar.ty
    return BETA_RULE(SPEC(pred, INST_TYPE([(v_ty, aty)], ax)))


def NOT_EX_TO_FORALL_NOT(not_th, pred):
    """|- ~(?v. body[v])   =>   |- !v. ~body[v]    where pred = \\v. body."""
    return MP(_spec_quant_ax(NOT_EX_TO_FORALL_NOT_AX, pred), not_th)


def NOT_FORALL_TO_EX_NOT(not_th, pred):
    """|- ~(!v. body[v])   =>   |- ?v. ~body[v].   Requires EM (classical)."""
    return MP(_spec_quant_ax(NOT_FORALL_TO_EX_NOT_AX, pred), not_th)


# ---------------------------------------------------------------------------
# COND -- polymorphic if-then-else.
#
#   COND b x y := @z:A. ((b = T) ==> z = x) /\ ((b = F) ==> z = y).
#
# At b = T the predicate has unique witness z = x (second conjunct vacuous
# since T = F is false). At b = F it has unique witness z = y. The two
# evaluation lemmas COND_T / COND_F discharge the SELECT.
# ---------------------------------------------------------------------------

_A_ty = aty
_a_A = Var("a", _A_ty)
_b_A = Var("b", _A_ty)
_b_bool = Var("b", bool_ty)
_x_A = Var("x", _A_ty)
_y_A = Var("y", _A_ty)
_z_A = Var("z", _A_ty)

COND_DEF = define(
    "COND",
    parse_type("bool -> A -> A -> A"),
    "\\b:bool. \\x:A. \\y:A. @z:A. ((b = T) ==> (z = x)) /\\ ((b = F) ==> (z = y))",
)
COND = mk_const("COND", [])


def mk_cond(b, x, y):
    """Build ``COND b x y`` with COND specialised at ``type_of(x)``."""
    from fusion import type_of

    xty = type_of(x)
    cond_inst = mk_const("COND", [(xty, aty)])
    return mk_app(cond_inst, b, x, y)


# Helper: |- T = F ==> p   for any boolean p. Used to discharge the vacuous
# branch in COND_T / COND_F.
def _T_eq_F_imp(p_term):
    th_TeqF = ASSUME(mk_eq(T, F))
    th_F = EQ_MP(th_TeqF, TRUTH)  # |- F   (under T = F)
    th_p = CONTR(p_term, th_F)
    return DISCH(mk_eq(T, F), th_p)


def _F_eq_T_imp(p_term):
    th_FeqT = ASSUME(mk_eq(F, T))
    th_F = EQ_MP(SYM(th_FeqT), TRUTH)
    th_p = CONTR(p_term, th_F)
    return DISCH(mk_eq(F, T), th_p)


def _prove_COND_T():
    # Goal: !x y. COND T x y = x.
    # Strategy: COND T x y = (\b x y. @z. ...) T x y; beta to get @z. ((T = T) ==> z = x) /\ ((T = F) ==> z = y).
    # Witness z := x: ((T = T) ==> x = x) /\ ((T = F) ==> x = y) holds.
    # SELECT_AX gives ((T = T) ==> sel = x) /\ ((T = F) ==> sel = y) at sel := @z. ...
    # First conjunct + REFL T + MP gives sel = x.
    # COND_DEF rewrite: COND T x y = sel. Combine to get COND T x y = x.

    # Beta-reduce COND T x y three times.
    cond_T_x_y = mk_app(COND, T, _x_A, _y_A)
    # COND = \b x y. @z. ...
    # COND_DEF: |- COND = (\b x y. @z. ...)
    cond_unfold = AP_TERM(_x_A.ty if False else None, COND_DEF) if False else None  # placeholder

    # Actually: from COND_DEF |- COND = body, AP_THM at T:
    cond_T_eq = AP_THM(COND_DEF, T)  # |- COND T = (\x y. ...) T -- wait, COND_DEF's RHS is \b x y. ..., so AP_THM at T beta is needed.
    # AP_THM: |- (COND) T = (\b x y. ...) T
    cond_T_beta = BETA_CONV(rand(cond_T_eq._concl))  # |- (\b x y. ...) T = \x y. (...with b:=T)
    cond_T = TRANS(cond_T_eq, cond_T_beta)  # |- COND T = \x y. (...with b:=T)

    cond_T_x_eq = AP_THM(cond_T, _x_A)
    cond_T_x_beta = BETA_CONV(rand(cond_T_x_eq._concl))
    cond_T_x = TRANS(cond_T_x_eq, cond_T_x_beta)  # |- COND T x = \y. (...)

    cond_T_x_y_eq = AP_THM(cond_T_x, _y_A)
    cond_T_x_y_beta = BETA_CONV(rand(cond_T_x_y_eq._concl))
    cond_full = TRANS(cond_T_x_y_eq, cond_T_x_y_beta)
    # |- COND T x y = @z. ((T = T) ==> z = x) /\ ((T = F) ==> z = y)

    sel_term = rand(cond_full._concl)  # the @z. ... = Comb(@, Abs(z, body))
    pred = sel_term.arg  # \z. body

    # Prove witness at z := x:
    # ((T = T) ==> x = x) /\ ((T = F) ==> x = y)
    refl_T = REFL(T)  # |- T = T
    refl_x = REFL(_x_A)  # |- x = x
    first_at_x = DISCH(mk_eq(T, T), refl_x)  # |- (T = T) ==> x = x
    second_at_x = _T_eq_F_imp(mk_eq(_x_A, _y_A))  # |- (T = F) ==> x = y
    pred_at_x = CONJ(first_at_x, second_at_x)  # |- pred-body[z:=x]

    # Want |- pred x  (i.e., (\z. body) x). Use SYM(BETA).
    pred_at_x_unbeta = EQ_MP(SYM(BETA_CONV(mk_app(pred, _x_A))), pred_at_x)
    # |- pred x

    # SELECT_AX: |- !P x. P x ==> P (@P). At our pred, x:
    sel_inst = INST_TYPE([(_A_ty, aty)], SELECT_AX)
    sel_imp = SPEC(_x_A, SPEC(pred, sel_inst))  # |- pred x ==> pred (@pred)
    pred_at_sel = MP(sel_imp, pred_at_x_unbeta)  # |- pred (@pred)

    # Beta-reduce pred (@pred) to ((T=T) ==> sel = x) /\ ((T=F) ==> sel = y)
    pred_at_sel_body = EQ_MP(BETA_CONV(mk_app(pred, sel_term)), pred_at_sel)
    # First conjunct: (T = T) ==> sel = x
    first_imp = CONJUNCT1(pred_at_sel_body)
    sel_eq_x = MP(first_imp, refl_T)  # |- sel = x

    # Combine: COND T x y = sel = x.
    cond_T_x_y_eq_x = TRANS(cond_full, sel_eq_x)
    return GENL([_x_A, _y_A], cond_T_x_y_eq_x)


def _prove_COND_F():
    cond_F_eq = AP_THM(COND_DEF, F)
    cond_F_beta = BETA_CONV(rand(cond_F_eq._concl))
    cond_F = TRANS(cond_F_eq, cond_F_beta)
    cond_F_x_eq = AP_THM(cond_F, _x_A)
    cond_F_x_beta = BETA_CONV(rand(cond_F_x_eq._concl))
    cond_F_x = TRANS(cond_F_x_eq, cond_F_x_beta)
    cond_F_x_y_eq = AP_THM(cond_F_x, _y_A)
    cond_F_x_y_beta = BETA_CONV(rand(cond_F_x_y_eq._concl))
    cond_full = TRANS(cond_F_x_y_eq, cond_F_x_y_beta)
    # |- COND F x y = @z. ((F = T) ==> z = x) /\ ((F = F) ==> z = y)

    sel_term = rand(cond_full._concl)
    pred = sel_term.arg

    refl_F = REFL(F)  # |- F = F
    refl_y = REFL(_y_A)
    first_at_y = _F_eq_T_imp(mk_eq(_y_A, _x_A))  # |- (F = T) ==> y = x
    second_at_y = DISCH(mk_eq(F, F), refl_y)  # |- (F = F) ==> y = y
    pred_at_y = CONJ(first_at_y, second_at_y)
    pred_at_y_unbeta = EQ_MP(SYM(BETA_CONV(mk_app(pred, _y_A))), pred_at_y)

    sel_inst = INST_TYPE([(_A_ty, aty)], SELECT_AX)
    sel_imp = SPEC(_y_A, SPEC(pred, sel_inst))
    pred_at_sel = MP(sel_imp, pred_at_y_unbeta)
    pred_at_sel_body = EQ_MP(BETA_CONV(mk_app(pred, sel_term)), pred_at_sel)

    second_imp = CONJUNCT2(pred_at_sel_body)
    sel_eq_y = MP(second_imp, refl_F)

    cond_F_x_y_eq_y = TRANS(cond_full, sel_eq_y)
    return GENL([_x_A, _y_A], cond_F_x_y_eq_y)


# AP_THM is needed below; import lazily to avoid reordering the long
# import block at the top.
from tactics import AP_THM

COND_T = _prove_COND_T()
COND_F = _prove_COND_F()


# ---------------------------------------------------------------------------
# Self-tests.
# ---------------------------------------------------------------------------


def _selftest():
    from fusion import concl, hyp
    from basics import aconv

    pv = Var("p", bool_ty)

    em_p = SPEC(pv, EXCLUDED_MIDDLE)
    assert aconv(concl(em_p), mk_or(pv, mk_not(pv)))
    assert hyp(em_p) == []

    nn = ASSUME(mk_not(mk_not(pv)))
    th = NOT_NOT_ELIM(nn)
    assert aconv(concl(th), pv)

    assert hyp(F_NEQ_T) == []
    assert aconv(concl(F_NEQ_T), mk_not(mk_eq(F, T)))


if __name__ == "__main__":
    _selftest()
    from parser import pp_thm

    print(f"EXCLUDED_MIDDLE: {pp_thm(EXCLUDED_MIDDLE)}")
    print(f"F_NEQ_T:         {pp_thm(F_NEQ_T)}")
    print(f"COND_DEF:        {pp_thm(COND_DEF)}")
    print(f"COND_T:          {pp_thm(COND_T)}")
    print(f"COND_F:          {pp_thm(COND_F)}")
    print("classical.py self-tests passed.")
