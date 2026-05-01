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
"""

from fusion import (
    Var,
    bool_ty, aty, mk_abs, mk_comb, mk_eq,
    rand, rator,
    REFL, TRANS, ASSUME, EQ_MP, INST_TYPE,
)
from axioms import T, F, SELECT_AX, mk_not, mk_or, mk_exists
from tactics import (
    AP_TERM, BETA_CONV, SYM, TRUTH, EQT_INTRO,
    SPEC, GEN, DISCH, MP, NOT_INTRO, NOT_ELIM,
    DISJ2, EXISTS, FUN_EXT,
    _select_const,
)
from proof import proof


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

    p.have("U_or: ((@x:bool. (x = F) \\/ t) = F) \\/ t")\
        .by_select(_SELECT_AX_BOOL, "U", "F", "U_F")
    p.have("V_or: ((@x:bool. (x = T) \\/ t) = T) \\/ t")\
        .by_select(_SELECT_AX_BOOL, "V", "T", "V_T")

    with p.cases_on("U_or"):
        with p.case("eq_uF: (@x:bool. (x = F) \\/ t) = F"):
            with p.cases_on("V_or"):
                with p.case("eq_vT: (@x:bool. (x = T) \\/ t) = T"):
                    with p.have("nott: ~t").proof():
                        with p.suppose("ht: t"):
                            F_eq_T = _diaconescu_F_eq_T(
                                _t_bool,
                                p.fact("eq_uF"), p.fact("eq_vT"), p.fact("ht"))
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
    """ |- ~~p   =>   |- p """
    p_t = rand(rand(th._concl))
    return MP(SPEC(p_t, NOT_NOT_ELIM_AX), th)


def NOT_EX_TO_FORALL_NOT(not_th, pred):
    """ |- ~(?v. body[v])   =>   |- !v. ~body[v]    where pred = \\v. body. """
    v_var = pred.bvar
    body_v = mk_comb(pred, v_var)
    body_v_term = rand(BETA_CONV(body_v)._concl)
    body_assume = ASSUME(body_v_term)
    ex_th = EXISTS(pred, v_var, body_assume)
    th_F = MP(NOT_ELIM(not_th), ex_th)
    return GEN(v_var, NOT_INTRO(DISCH(body_v_term, th_F)))


def NOT_FORALL_TO_EX_NOT(not_th, pred):
    """ |- ~(!v. body[v])   =>   |- ?v. ~body[v].   Requires EM (classical). """
    v_var = pred.bvar
    body_v = mk_comb(pred, v_var)
    body_v_term = rand(BETA_CONV(body_v)._concl)
    not_pred = mk_abs(v_var, mk_not(body_v_term))
    target = mk_exists(v_var, mk_not(body_v_term))
    h_not_target = ASSUME(mk_not(target))
    forall_nn = NOT_EX_TO_FORALL_NOT(h_not_target, not_pred)
    spec_nn = SPEC(v_var, forall_nn)
    body_v_th = NOT_NOT_ELIM(spec_nn)
    forall_body = GEN(v_var, body_v_th)
    th_F = MP(NOT_ELIM(not_th), forall_body)
    th_nn_target = NOT_INTRO(DISCH(mk_not(target), th_F))
    return NOT_NOT_ELIM(th_nn_target)


# ---------------------------------------------------------------------------
# Self-tests.
# ---------------------------------------------------------------------------

def _selftest():
    from fusion import aconv, concl, hyp
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
    print("classical.py self-tests passed.")
