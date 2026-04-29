"""Derived boolean-logic inference rules and classical theorems.

Built on the primitive HOL Light kernel in ``fusion.py`` plus the boolean
infrastructure / 3 logical axioms (ETA, SELECT, INFINITY) from ``axioms.py``.

Provides:
  * Pretty-printer (``pp``, ``pp_thm``).
  * Standard derived rules: AP_TERM, AP_THM, BETA_CONV, BETA_NORM, SYM,
    TRUTH, EQT_ELIM/INTRO, SPEC, GEN, CONJ, CONJUNCT1/2, DISCH, MP, UNDISCH,
    CONTR, NOT_ELIM/INTRO, EQF_ELIM/INTRO, DISJ1/2, DISJ_CASES, EXISTS.
  * EXCLUDED_MIDDLE   |- !t. t \\/ ~t   (proved from SELECT_AX + ETA_AX
    via Diaconescu's argument; mirrors HOL Light's class.ml).
  * Classical helpers: NOT_NOT_ELIM, NOT_EX_TO_FORALL_NOT, NOT_FORALL_TO_EX_NOT.
"""

from fusion import (
    Var, Const, Comb, Abs,
    bool_ty, aty, bty, mk_abs, mk_comb, mk_const, mk_eq, mk_fun_ty,
    type_of, dest_eq,
    rator, rand, freesl, variant, aconv,
    REFL, TRANS, MK_COMB, ABS, BETA, ASSUME, EQ_MP,
    DEDUCT_ANTISYM_RULE, INST, INST_TYPE,
    concl, hyp, HolError, new_basic_definition,
)
from axioms import (
    T, F,
    T_DEF, AND_DEF, IMP_DEF, FORALL_DEF, EXISTS_DEF, F_DEF, NOT_DEF,
    SELECT_AX, ETA_AX,
    mk_and, mk_imp, mk_forall, mk_exists, mk_not,
)


# ---------------------------------------------------------------------------
# Pretty-printer (display only -- never used by proofs).
# ---------------------------------------------------------------------------

_INFIX = {"=", "/\\", "==>", "\\/"}

def pp(tm):
    if isinstance(tm, Var):
        return tm.name
    if isinstance(tm, Const):
        return tm.name
    if isinstance(tm, Abs):
        return f"(\\{tm.bvar.name}. {pp(tm.body)})"
    if isinstance(tm, Comb):
        if (isinstance(tm.fun, Const) and tm.fun.name in {"!", "?"}
                and isinstance(tm.arg, Abs)):
            return f"({tm.fun.name}{tm.arg.bvar.name}. {pp(tm.arg.body)})"
        if isinstance(tm.fun, Const) and tm.fun.name == "~":
            return f"~{pp(tm.arg)}"
        if isinstance(tm.fun, Comb) and isinstance(tm.fun.fun, Const) \
                and tm.fun.fun.name in _INFIX:
            op = tm.fun.fun.name
            a = pp(tm.fun.arg)
            b = pp(tm.arg)
            return f"({a} {op} {b})"
        return f"({pp(tm.fun)} {pp(tm.arg)})"
    return repr(tm)

def pp_thm(th):
    asl = hyp(th)
    h = "" if not asl else ", ".join(pp(a) for a in asl) + " "
    return f"{h}|- {pp(concl(th))}"


# ---------------------------------------------------------------------------
# Congruence helpers.
# ---------------------------------------------------------------------------

def AP_TERM(tm, th):
    """ |- a = b   =>   |- f a = f b """
    return MK_COMB(REFL(tm), th)

def AP_THM(th, tm):
    """ |- f = g   =>   |- f x = g x """
    return MK_COMB(th, REFL(tm))


# General beta on (\x. body) t for any t.
# Primitive BETA only fires when arg == bvar; we lift via INST.

def BETA_CONV(tm):
    r""" |- (\x. body) t = body[t/x] """
    if not isinstance(tm, Comb) or not isinstance(tm.fun, Abs):
        raise HolError("BETA_CONV: not a beta-redex")
    bvar = tm.fun.bvar
    base = BETA(mk_comb(tm.fun, bvar))      # |- (\x. body) x = body
    if tm.arg == bvar:
        return base
    return INST([(tm.arg, bvar)], base)     # |- (\x. body) t = body[t/x]


def BETA_NORM(tm):
    """ |- tm = (full beta normal form of tm) """
    if isinstance(tm, Comb):
        f_th = BETA_NORM(tm.fun)
        a_th = BETA_NORM(tm.arg)
        comb_th = MK_COMB(f_th, a_th)
        new_comb = rand(comb_th._concl)
        if isinstance(new_comb, Comb) and isinstance(new_comb.fun, Abs):
            beta_th = BETA_CONV(new_comb)
            after_th = BETA_NORM(rand(beta_th._concl))
            return TRANS(comb_th, TRANS(beta_th, after_th))
        return comb_th
    if isinstance(tm, Abs):
        body_th = BETA_NORM(tm.body)
        return ABS(tm.bvar, body_th)
    return REFL(tm)


# Symmetry of equality.

def SYM(th):
    """ |- a = b   =>   |- b = a """
    a, _ = dest_eq(th._concl)
    eq_op = rator(rator(th._concl))
    th1 = AP_TERM(eq_op, th)
    th2 = MK_COMB(th1, REFL(a))
    return EQ_MP(th2, REFL(a))


# TRUTH: |- T

_p_bool = Var("p", bool_ty)
TRUTH = EQ_MP(SYM(T_DEF), REFL(mk_abs(_p_bool, _p_bool)))


def EQT_ELIM(th):
    """ |- p = T   =>   |- p """
    return EQ_MP(SYM(th), TRUTH)

def EQT_INTRO(th):
    """ |- p   =>   |- p = T """
    return DEDUCT_ANTISYM_RULE(th, TRUTH)


# SPEC, GEN -- universal elimination / introduction.

def SPEC(t, th):
    """ |- !x. P[x]   =>   |- P[t] """
    pred = rand(th._concl)
    if not isinstance(pred, Abs):
        raise HolError("SPEC: not a forall theorem")
    bvar = pred.bvar
    fdef = INST_TYPE([(bvar.ty, aty)], FORALL_DEF)
    eq1 = AP_THM(fdef, pred)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    pred_eq_lamT = EQ_MP(eq2, th)
    appT = AP_THM(pred_eq_lamT, t)
    lhs_red = BETA_CONV(mk_comb(pred, t))
    rhs_red = BETA_CONV(rand(appT._concl))
    p_eq_T = TRANS(SYM(lhs_red), TRANS(appT, rhs_red))
    return EQT_ELIM(p_eq_T)


def GEN(v, th):
    """ |- P[v]   =>   |- !v. P[v]    (v not free in the hypotheses) """
    if not isinstance(v, Var):
        raise HolError("GEN: not a variable")
    th_eqT = EQT_INTRO(th)
    th_abs = ABS(v, th_eqT)
    pred = mk_abs(v, th._concl)
    fdef = INST_TYPE([(v.ty, aty)], FORALL_DEF)
    eq1 = AP_THM(fdef, pred)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    return EQ_MP(SYM(eq2), th_abs)


# Conjunction.

def _bbb_var(name, avoid):
    bbb = mk_fun_ty(bool_ty, mk_fun_ty(bool_ty, bool_ty))
    return variant(avoid, Var(name, bbb))

def CONJ(th_p, th_q):
    r""" |- p, |- q   =>   |- p /\ q """
    p_t, q_t = th_p._concl, th_q._concl
    eq1 = AP_THM(AND_DEF, p_t)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    eq3 = AP_THM(eq2, q_t)
    eq4 = TRANS(eq3, BETA_CONV(rand(eq3._concl)))
    avoid = freesl(list(th_p._asl) + list(th_q._asl) + [p_t, q_t])
    fv = _bbb_var("f", avoid)
    eqT_p = EQT_INTRO(th_p)
    eqT_q = EQT_INTRO(th_q)
    th_fpq = MK_COMB(AP_TERM(fv, eqT_p), eqT_q)
    th_lam = ABS(fv, th_fpq)
    return EQ_MP(SYM(eq4), th_lam)


def _CONJUNCT_proj(th, take_first):
    conj = th._concl
    p_t = rand(rator(conj))
    q_t = rand(conj)
    eq1 = AP_THM(AND_DEF, p_t)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    eq3 = AP_THM(eq2, q_t)
    eq4 = TRANS(eq3, BETA_CONV(rand(eq3._concl)))
    th_eq = EQ_MP(eq4, th)
    avoid = freesl(list(th._asl) + [p_t, q_t])
    a_v = variant(avoid, Var("a", bool_ty))
    b_v = variant(avoid + [a_v], Var("b", bool_ty))
    proj = mk_abs(a_v, mk_abs(b_v, a_v if take_first else b_v))
    th_app = AP_THM(th_eq, proj)
    lhs_app, rhs_app = dest_eq(th_app._concl)
    def _reduce(side, fst, snd):
        s1 = BETA_CONV(side)
        proj_fst = rator(rand(s1._concl))
        s2_inner = BETA_CONV(proj_fst)
        s2 = MK_COMB(s2_inner, REFL(snd))
        s3 = BETA_CONV(rand(s2._concl))
        return TRANS(s1, TRANS(s2, s3))
    lhs_norm = _reduce(lhs_app, p_t, q_t)
    rhs_norm = _reduce(rhs_app, T, T)
    p_or_q_eq_T = TRANS(SYM(lhs_norm), TRANS(th_app, rhs_norm))
    return EQT_ELIM(p_or_q_eq_T)

def CONJUNCT1(th):
    r""" |- p /\ q   =>   |- p """
    return _CONJUNCT_proj(th, take_first=True)

def CONJUNCT2(th):
    r""" |- p /\ q   =>   |- q """
    return _CONJUNCT_proj(th, take_first=False)


# DISCH, MP, UNDISCH.

def _imp_eq(p_t, q_t):
    r"""Build |- (p ==> q) = (p /\ q = p) from IMP_DEF."""
    eq1 = AP_THM(IMP_DEF, p_t)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    eq3 = AP_THM(eq2, q_t)
    return TRANS(eq3, BETA_CONV(rand(eq3._concl)))

def DISCH(p_t, th):
    """ asl |- q   =>   asl - {p}  |-  p ==> q """
    th1 = CONJ(ASSUME(p_t), th)
    th2 = CONJUNCT1(ASSUME(mk_and(p_t, th._concl)))
    th3 = DEDUCT_ANTISYM_RULE(th1, th2)
    eq = _imp_eq(p_t, th._concl)
    return EQ_MP(SYM(eq), th3)

def MP(th_imp, th_p):
    """ |- p ==> q,  |- p   =>   |- q """
    p_t = th_p._concl
    if not isinstance(th_imp._concl, Comb) or not isinstance(th_imp._concl.fun, Comb):
        raise HolError("MP: first theorem is not an implication")
    q_t = rand(th_imp._concl)
    eq = _imp_eq(p_t, q_t)
    th_pq_eq_p = EQ_MP(eq, th_imp)
    th_pq = EQ_MP(SYM(th_pq_eq_p), th_p)
    return CONJUNCT2(th_pq)

def UNDISCH(th):
    """ |- p ==> q   =>   {p} |- q """
    p_t = rand(rator(th._concl))
    return MP(th, ASSUME(p_t))


# Falsity / contradiction / negation.

def CONTR(tm, th_F):
    """ |- F   =>   |- tm    (for any boolean tm) """
    th_all = EQ_MP(F_DEF, th_F)
    return SPEC(tm, th_all)

def NOT_ELIM(th):
    """ |- ~p   =>   |- p ==> F """
    p_t = rand(th._concl)
    eq1 = AP_THM(NOT_DEF, p_t)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    return EQ_MP(eq2, th)

def NOT_INTRO(th_imp_F):
    """ |- p ==> F   =>   |- ~p """
    p_t = rand(rator(th_imp_F._concl))
    eq1 = AP_THM(NOT_DEF, p_t)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    return EQ_MP(SYM(eq2), th_imp_F)

def EQF_INTRO(th_not):
    """ |- ~p   =>   |- p = F """
    p_t = rand(th_not._concl)
    th_p = ASSUME(p_t)
    th_F = MP(NOT_ELIM(th_not), th_p)
    th_fp = CONTR(p_t, ASSUME(F))
    return DEDUCT_ANTISYM_RULE(th_F, th_fp)

def EQF_ELIM(th):
    """ |- p = F   =>   |- ~p """
    p_t, _ = dest_eq(th._concl)
    th_imp_F = DISCH(p_t, EQ_MP(th, ASSUME(p_t)))
    return NOT_INTRO(th_imp_F)


# Disjunction.   OR_DEF :  (\/) = \p q. !r. (p ==> r) ==> (q ==> r) ==> r.

_p_b = Var("p", bool_ty)
_q_b = Var("q", bool_ty)
_r_b = Var("r", bool_ty)
_bbb = mk_fun_ty(bool_ty, mk_fun_ty(bool_ty, bool_ty))
OR_DEF = new_basic_definition(
    mk_eq(Var("\\/", _bbb),
          mk_abs(_p_b, mk_abs(_q_b,
              mk_forall(_r_b,
                  mk_imp(mk_imp(_p_b, _r_b),
                         mk_imp(mk_imp(_q_b, _r_b), _r_b)))))))

def mk_or(a, b):
    return mk_comb(mk_comb(mk_const("\\/", []), a), b)

def _or_unfold(p_t, q_t):
    """ |- (p \\/ q) = (!r. (p==>r) ==> (q==>r) ==> r) """
    eq1 = AP_THM(OR_DEF, p_t)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    eq3 = AP_THM(eq2, q_t)
    return TRANS(eq3, BETA_CONV(rand(eq3._concl)))

def DISJ1(th_p, q_t):
    """ |- p   =>   |- p \\/ q """
    p_t = th_p._concl
    avoid = freesl(list(th_p._asl) + [p_t, q_t])
    r_v = variant(avoid, Var("r", bool_ty))
    p_imp_r = mk_imp(p_t, r_v)
    q_imp_r = mk_imp(q_t, r_v)
    th_r = MP(ASSUME(p_imp_r), th_p)
    th_inner = DISCH(p_imp_r, DISCH(q_imp_r, th_r))
    th_gen = GEN(r_v, th_inner)
    return EQ_MP(SYM(_or_unfold(p_t, q_t)), th_gen)

def DISJ2(p_t, th_q):
    """ |- q   =>   |- p \\/ q """
    q_t = th_q._concl
    avoid = freesl(list(th_q._asl) + [p_t, q_t])
    r_v = variant(avoid, Var("r", bool_ty))
    p_imp_r = mk_imp(p_t, r_v)
    q_imp_r = mk_imp(q_t, r_v)
    th_r = MP(ASSUME(q_imp_r), th_q)
    th_inner = DISCH(p_imp_r, DISCH(q_imp_r, th_r))
    th_gen = GEN(r_v, th_inner)
    return EQ_MP(SYM(_or_unfold(p_t, q_t)), th_gen)

def DISJ_CASES(th_or, th_p_imp, th_q_imp):
    """ |- p \\/ q,  asl_p, p |- r,  asl_q, q |- r   =>   asl |- r """
    p_t = rand(rator(th_or._concl))
    q_t = rand(th_or._concl)
    r_t = rand(th_p_imp._concl)
    th_unfold = EQ_MP(_or_unfold(p_t, q_t), th_or)
    th_spec = SPEC(r_t, th_unfold)
    return MP(MP(th_spec, th_p_imp), th_q_imp)


# Tiny rewriting helpers.

NOT_CONST = mk_const("~", [])

def _eq_const_for(ty):
    return mk_const("=", [(ty, aty)])

def MK_EQ(eq_l, eq_r):
    """ |- a = a',  |- b = b'   =>   |- (a = b) = (a' = b') """
    return MK_COMB(AP_TERM(_eq_const_for(type_of(dest_eq(eq_l._concl)[0])), eq_l), eq_r)

def NE_SYM(th):
    """ |- ~(a = b)   =>   |- ~(b = a) """
    a, b = dest_eq(rand(th._concl))
    th_F = MP(NOT_ELIM(th), SYM(ASSUME(mk_eq(b, a))))
    return NOT_INTRO(DISCH(mk_eq(b, a), th_F))

def REWRITE_NE(th_ne, eq_l, eq_r):
    """ |- ~(a = b),  |- a = a',  |- b = b'   =>   |- ~(a' = b') """
    eq_eq = MK_EQ(eq_l, eq_r)
    return EQ_MP(AP_TERM(NOT_CONST, eq_eq), th_ne)


# Existential introduction.

def EXISTS(pred, witness, th):
    """ pred = Abs(v, body)   ; th : |- body[witness/v]  =>   |- ?v. body """
    if not isinstance(pred, Abs):
        raise HolError("EXISTS: pred must be an Abs")
    v_var = pred.bvar
    pred_w = mk_comb(pred, witness)
    th_pw = EQ_MP(SYM(BETA_CONV(pred_w)), th)
    avoid = freesl(list(th._asl) + [pred, witness])
    q_var = variant(avoid, Var("q", bool_ty))
    pred_v = mk_comb(pred, v_var)
    forall_inner = mk_forall(v_var, mk_imp(pred_v, q_var))
    th_imp_q = SPEC(witness, ASSUME(forall_inner))
    th_q     = MP(th_imp_q, th_pw)
    th_disch = DISCH(forall_inner, th_q)
    th_gen   = GEN(q_var, th_disch)
    edef = INST_TYPE([(v_var.ty, aty)], EXISTS_DEF)
    eq1 = AP_THM(edef, pred)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    return EQ_MP(SYM(eq2), th_gen)


# ---------------------------------------------------------------------------
# Boolean extensionality.   |- !P Q. (!x. P x = Q x) ==> P = Q.
# Combines ABS over the pointwise equality with two ETA_AX rewrites.
# ---------------------------------------------------------------------------

def _select_const(ty):
    """The (@) constant at type (ty -> bool) -> ty."""
    return mk_const("@", [(ty, aty)])


def FUN_EXT(th_pointwise):
    """ asl |- !x. f x = g x   =>   asl |- f = g.
        f, g are recovered by `rator` of the two sides, so the pointwise
        equation must literally have the shape `f x = g x` (not e.g.
        `f x = T`).  x must not be free in any hypothesis. """
    forall_term = th_pointwise._concl
    pred = rand(forall_term)
    if not isinstance(pred, Abs):
        raise HolError("FUN_EXT: not a forall theorem")
    x_var = pred.bvar
    pw = SPEC(x_var, th_pointwise)            # asl |- f x = g x
    f_x, g_x = dest_eq(pw._concl)
    if not (isinstance(f_x, Comb) and isinstance(g_x, Comb)):
        raise HolError("FUN_EXT: pointwise equation must be of form f x = g x")
    abs_eq = ABS(x_var, pw)                   # asl |- (\x. f x) = (\x. g x)
    f_term = rator(f_x)
    g_term = rator(g_x)
    a_ty = x_var.ty
    b_ty = type_of(f_x)
    eta_inst = INST_TYPE([(a_ty, aty), (b_ty, bty)], ETA_AX)
    eta_f = SPEC(f_term, eta_inst)            # |- (\x. f x) = f
    eta_g = SPEC(g_term, eta_inst)            # |- (\x. g x) = g
    return TRANS(SYM(eta_f), TRANS(abs_eq, eta_g))


# ---------------------------------------------------------------------------
# F != T  (i.e. |- ~(F = T)).
# Proof: assume F = T.  Then T (= TRUTH) gives F by EQ_MP(SYM(_), TRUTH).
# Discharge to F ==> ... and convert to negation.
# ---------------------------------------------------------------------------

def _prove_F_neq_T():
    h = ASSUME(mk_eq(F, T))                      # {F=T} |- F = T
    th_F = EQ_MP(SYM(h), TRUTH)                   # {F=T} |- F
    return NOT_INTRO(DISCH(mk_eq(F, T), th_F))    # |- ~(F = T)

F_NEQ_T = _prove_F_neq_T()


# ---------------------------------------------------------------------------
# EXCLUDED_MIDDLE   |- !t:bool. t \/ ~t.
#
# Diaconescu's argument (mirrors HOL Light's class.ml).
#
# Fix t.  Define
#     U = \x:bool. (x = F) \/ t
#     V = \x:bool. (x = T) \/ t.
# Both are inhabited (U F, V T), so SELECT_AX gives
#     U (@U)   :  (@U = F) \/ t
#     V (@V)   :  (@V = T) \/ t.
# Case-split: if either disjunction yields t, we are done by DISJ1.
# Otherwise @U = F and @V = T.  Suppose t held.  Then for every x,
# the disjunction (x=F)\/t (resp. (x=T)\/t) holds, so U = (\x. T) = V
# pointwise; by extensionality U = V, hence @U = @V, contradicting
# F != T.  So ~t, and DISJ2 finishes.
# ---------------------------------------------------------------------------

def _prove_excluded_middle():
    t_var = Var("t", bool_ty)
    x_var = Var("x", bool_ty)

    # U = \x. (x = F) \/ t,    V = \x. (x = T) \/ t.
    U_body = mk_or(mk_eq(x_var, F), t_var)
    V_body = mk_or(mk_eq(x_var, T), t_var)
    U = mk_abs(x_var, U_body)
    V = mk_abs(x_var, V_body)

    bool_to_bool = mk_fun_ty(bool_ty, bool_ty)
    select_b = _select_const(bool_ty)             # (@) : (bool->bool) -> bool
    sel_U = mk_comb(select_b, U)                  # @U
    sel_V = mk_comb(select_b, V)                  # @V

    # ----- (a)  derive |- U F   and   |- V T. -----
    # |- F = F  ;  DISJ1 gives |- (F = F) \/ t  ;  EQ_MP via BETA gives |- U F.
    refl_F = REFL(F)                              # |- F = F
    or_FF_t = DISJ1(refl_F, t_var)                # |- (F = F) \/ t
    UF_term = mk_comb(U, F)
    UF_th = EQ_MP(SYM(BETA_CONV(UF_term)), or_FF_t)   # |- U F

    refl_T = REFL(T)
    or_TT_t = DISJ1(refl_T, t_var)
    VT_term = mk_comb(V, T)
    VT_th = EQ_MP(SYM(BETA_CONV(VT_term)), or_TT_t)   # |- V T

    # ----- (b)  apply SELECT_AX to extract U(@U), V(@V). -----
    # SELECT_AX : !P x. P x ==> P (@P).
    sel_inst = INST_TYPE([(bool_ty, aty)], SELECT_AX)
    sel_U_imp = SPEC(F, SPEC(U, sel_inst))        # |- U F ==> U (@U)
    U_at_selU = MP(sel_U_imp, UF_th)              # |- U (@U)
    sel_V_imp = SPEC(T, SPEC(V, sel_inst))        # |- V T ==> V (@V)
    V_at_selV = MP(sel_V_imp, VT_th)              # |- V (@V)

    # Unfold U(@U) into (sel_U = F) \/ t  and similarly for V.
    U_at_selU_term = mk_comb(U, sel_U)
    U_or = EQ_MP(BETA_CONV(U_at_selU_term), U_at_selU)   # |- (sel_U = F) \/ t

    V_at_selV_term = mk_comb(V, sel_V)
    V_or = EQ_MP(BETA_CONV(V_at_selV_term), V_at_selV)   # |- (sel_V = T) \/ t

    goal = mk_or(t_var, mk_not(t_var))            # t \/ ~t

    # ----- (c)  Case-split on (sel_U = F) \/ t. -----
    # Branch 1: sel_U = F.  Recurse on V_or.
    eq_uF   = ASSUME(mk_eq(sel_U, F))             # {sel_U=F} |- sel_U = F
    # Branch 1.1: sel_V = T.  Use Diaconescu argument.
    eq_vT   = ASSUME(mk_eq(sel_V, T))             # {sel_V=T} |- sel_V = T

    # Sub-proof: {sel_U=F, sel_V=T, t} |- F.
    h_t = ASSUME(t_var)                           # {t} |- t

    # From t, prove |- !x. U x = (\x. T) x and similarly for V.
    lam_T = mk_abs(x_var, T)
    UxT_pointwise = _pointwise_eq_T(U, x_var, U_body, h_t, t_var, lam_T)
    VxT_pointwise = _pointwise_eq_T(V, x_var, V_body, h_t, t_var, lam_T)

    # By FUN_EXT: {t} |- U = (\x. T) and similarly V = (\x. T).
    U_eq_lamT = FUN_EXT(UxT_pointwise)            # {t} |- U = (\x. T)
    V_eq_lamT = FUN_EXT(VxT_pointwise)            # {t} |- V = (\x. T)
    U_eq_V    = TRANS(U_eq_lamT, SYM(V_eq_lamT))  # {t} |- U = V
    selU_eq_selV = AP_TERM(select_b, U_eq_V)      # {t} |- @U = @V

    # Now combine with {sel_U=F, sel_V=T} to get F = T:
    #   F = sel_U = sel_V = T.
    F_eq_selU = SYM(eq_uF)                        # {sel_U=F} |- F = sel_U
    selV_eq_T = eq_vT                             # {sel_V=T} |- sel_V = T
    F_eq_selV = TRANS(F_eq_selU, selU_eq_selV)    # {sel_U=F, t} |- F = sel_V
    F_eq_T    = TRANS(F_eq_selV, selV_eq_T)       # {sel_U=F, sel_V=T, t} |- F = T

    th_F = MP(NOT_ELIM(F_NEQ_T), F_eq_T)          # {sel_U=F, sel_V=T, t} |- F
    not_t = NOT_INTRO(DISCH(t_var, th_F))         # {sel_U=F, sel_V=T} |- ~t
    or_t_nt_from_uF_vT = DISJ2(t_var, not_t)      # {sel_U=F, sel_V=T} |- t \/ ~t

    # Branch 1: now DISJ_CASES on V_or  (using sel_V=T branch + t branch).
    branch_V_T = DISCH(mk_eq(sel_V, T), or_t_nt_from_uF_vT)   # {sel_U=F} |- (sel_V=T) ==> goal
    branch_V_t = DISCH(t_var, DISJ1(ASSUME(t_var), mk_not(t_var)))   # |- t ==> goal
    or_t_nt_from_uF = DISJ_CASES(V_or, branch_V_T, branch_V_t)
    # or_t_nt_from_uF : {sel_U=F} |- t \/ ~t.

    # Branch 0: t.   Done immediately.
    or_t_nt_from_t = DISJ1(ASSUME(t_var), mk_not(t_var))      # {t} |- t \/ ~t

    # Combine via DISJ_CASES on U_or.
    branch_U_F = DISCH(mk_eq(sel_U, F), or_t_nt_from_uF)      # |- (sel_U=F) ==> goal
    branch_U_t = DISCH(t_var, or_t_nt_from_t)                 # |- t ==> goal
    final_for_t = DISJ_CASES(U_or, branch_U_F, branch_U_t)    # |- t \/ ~t

    return GEN(t_var, final_for_t)


def _pointwise_eq_T(F_lambda, x_var, body, h_t, t_var, lam_T):
    """Given `F_lambda` = `\\x. body` where `body` has shape `(... \\/ t)`,
    return  {t} |- !x. F_lambda x = (\\x. T) x.

    The RHS is left as the application `(\\x. T) x` (rather than its beta
    normal form `T`) so that FUN_EXT can recognise it as the application of
    a function, recover that function via ETA, and conclude
    F_lambda = (\\x. T).
    """
    lhs_disj = rand(rator(body))                  # `(x = F)` or `(x = T)`
    body_th = DISJ2(lhs_disj, h_t)                # {t} |- body
    Fx = mk_comb(F_lambda, x_var)
    Fx_eq_body = BETA_CONV(Fx)                    # |- F_lambda x = body
    body_eq_T  = EQT_INTRO(body_th)               # {t} |- body = T
    Fx_eq_T    = TRANS(Fx_eq_body, body_eq_T)     # {t} |- F_lambda x = T
    # Rewrite RHS T  to  (\x. T) x  via SYM(BETA_CONV).
    lamT_x = mk_comb(lam_T, x_var)
    T_eq_lamTx = SYM(BETA_CONV(lamT_x))           # |- T = (\x. T) x
    Fx_eq_lamTx = TRANS(Fx_eq_T, T_eq_lamTx)      # {t} |- F_lambda x = (\x. T) x
    return GEN(x_var, Fx_eq_lamTx)


EXCLUDED_MIDDLE = _prove_excluded_middle()


# ---------------------------------------------------------------------------
# Classical helpers built on EM.
# ---------------------------------------------------------------------------

def NOT_NOT_ELIM(th):
    """ |- ~~p   =>   |- p """
    p_t = rand(rand(th._concl))
    em_p = SPEC(p_t, EXCLUDED_MIDDLE)
    branch_p  = DISCH(p_t, ASSUME(p_t))
    branch_np = DISCH(mk_not(p_t),
                       CONTR(p_t, MP(NOT_ELIM(th), ASSUME(mk_not(p_t)))))
    return DISJ_CASES(em_p, branch_p, branch_np)


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
    pv = Var("p", bool_ty)
    qv = Var("q", bool_ty)

    # SYM
    th = ASSUME(mk_eq(pv, qv))
    assert aconv(concl(SYM(th)), mk_eq(qv, pv))

    # TRUTH
    assert aconv(concl(TRUTH), T)

    # EQT_INTRO / EQT_ELIM round-trip
    th_p = ASSUME(pv)
    th_back = EQT_ELIM(EQT_INTRO(th_p))
    assert aconv(concl(th_back), pv)

    # SPEC of EXCLUDED_MIDDLE
    em_p = SPEC(pv, EXCLUDED_MIDDLE)
    assert aconv(concl(em_p), mk_or(pv, mk_not(pv)))
    assert hyp(em_p) == []

    # NOT_NOT_ELIM
    nn = ASSUME(mk_not(mk_not(pv)))
    th = NOT_NOT_ELIM(nn)
    assert aconv(concl(th), pv)

    # F != T is unconditional
    assert hyp(F_NEQ_T) == []
    assert aconv(concl(F_NEQ_T), mk_not(mk_eq(F, T)))


if __name__ == "__main__":
    _selftest()
    print(f"EXCLUDED_MIDDLE: {pp_thm(EXCLUDED_MIDDLE)}")
    print(f"F_NEQ_T:         {pp_thm(F_NEQ_T)}")
    print("logic.py self-tests passed.")
