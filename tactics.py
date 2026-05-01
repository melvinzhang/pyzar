"""Derived inference rules + higher-level tactics.

Built on the primitive HOL Light kernel in ``fusion.py`` plus the boolean
infrastructure / 3 logical axioms (ETA, SELECT, INFINITY) from ``axioms.py``.

Provides:

  * Derived rules: AP_TERM, AP_THM, BETA_CONV, BETA_NORM, SYM, TRUTH,
    EQT_ELIM/INTRO, SPEC, GEN, CONJ, CONJUNCT1/2, DISCH, MP, UNDISCH,
    CONTR, NOT_ELIM/INTRO, EQF_ELIM/INTRO, DISJ1/2, DISJ_CASES, EXISTS,
    FUN_EXT, ELIM_EX, list-form combinators (SPECL, GENL, ...).
  * Rewriting tactics: REWRITE_CONV, REWRITE_RULE, REWRITE_PROVE, BETA_RULE.
  * AC tactics: AC_NORM, AC_PROVE, REWRITE_AC_PROVE.

The classical theorems built on top (``F_NEQ_T``, ``EXCLUDED_MIDDLE``,
``NOT_NOT_ELIM``, ``NOT_EX_TO_FORALL_NOT``, ``NOT_FORALL_TO_EX_NOT``) live
in ``classical.py``, which sits above ``proof.py`` so their proofs can use
the declarative DSL.

Pretty-printing lives in ``parser.py`` (``pp``, ``pp_thm``) since it's
surface syntax.
"""

from fusion import (
    Var, Const, Comb, Abs, thm,
    bool_ty, aty, bty, mk_abs, mk_comb, mk_const, mk_eq, mk_fun_ty,
    type_of, dest_eq,
    rator, rand, freesl, variant, aconv,
    REFL, TRANS, MK_COMB, ABS, BETA, ASSUME, EQ_MP,
    DEDUCT_ANTISYM_RULE, INST, INST_TYPE,
    concl, hyp, HolError,
)
from axioms import (
    T, F,
    T_DEF, AND_DEF, OR_DEF, IMP_DEF, FORALL_DEF, EXISTS_DEF, F_DEF, NOT_DEF,
    SELECT_AX, ETA_AX,
    mk_and, mk_or, mk_imp, mk_forall, mk_exists, mk_not, mk_select,
)


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


# Disjunction rules.   OR_DEF lives in axioms.py.

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

def _subst_term(old, new, tm):
    """Replace every occurrence of `old` (a term) with `new` inside `tm`."""
    if tm == old:
        return new
    if isinstance(tm, Comb):
        f2 = _subst_term(old, new, tm.fun)
        a2 = _subst_term(old, new, tm.arg)
        if f2 is tm.fun and a2 is tm.arg:
            return tm
        return mk_comb(f2, a2)
    if isinstance(tm, Abs):
        b2 = _subst_term(old, new, tm.body)
        if b2 is tm.body:
            return tm
        return mk_abs(tm.bvar, b2)
    return tm


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
# List-form combinators -- shorthand for repeated SPEC/GEN/DISCH/TRANS chains.
#
#   SPECL([a, b, c], thm)   = SPEC(c, SPEC(b, SPEC(a, thm)))
#   GENL([x, y, z], thm)    yields  |- !x y z. concl
#   DISCHL([h1, h2], thm)   yields  |- h1 ==> h2 ==> concl
#   TRANS_CHAIN([t1,...,tn]) chains TRANS over a list of equalities.
# ---------------------------------------------------------------------------

def SPECL(args, th):
    for a in args:
        th = SPEC(a, th)
    return th

def GENL(vars, th):
    for v in reversed(vars):
        th = GEN(v, th)
    return th

def DISCHL(hyps, th):
    for h in reversed(hyps):
        th = DISCH(h, th)
    return th

def TRANS_CHAIN(thms):
    if not thms:
        raise HolError("TRANS_CHAIN: empty list")
    result = thms[0]
    for t in thms[1:]:
        result = TRANS(result, t)
    return result


# ---------------------------------------------------------------------------
# MP_LIST -- forward composition over a mixed list of terms / theorems.
#
#   MP_LIST(thm, [a1, a2, ...])  applies SPEC for each Term-typed entry and
#   MP for each thm-typed entry, in order.  Replaces nested
#   `MP(MP(SPECL([a, b, c], thm), th1), th2)` with
#   `MP_LIST(thm, [a, b, c, th1, th2])`.
# ---------------------------------------------------------------------------

def MP_LIST(th, args):
    for a in args:
        if isinstance(a, thm):
            th = MP(th, a)
        else:
            th = SPEC(a, th)
    return th


# ---------------------------------------------------------------------------
# CASE_OR -- structured case analysis on a disjunction.
#
#   CASE_OR(or_thm, (h1, prover1), (h2, prover2))   is shorthand for
#       DISJ_CASES(or_thm, DISCH(h1, prover1(ASSUME(h1))),
#                          DISCH(h2, prover2(ASSUME(h2)))).
#
#   Each prover receives `ASSUME(h)` and returns the conclusion theorem.
# ---------------------------------------------------------------------------

def EXISTS_AT(witness, th):
    """ |- body  =>  |- ?v. body[v/witness]   for a fresh `v`.

    Picks a fresh variable `v` of `witness`'s type, replaces every occurrence
    of `witness` in th's conclusion with `v`, and applies EXISTS.  Use when
    every occurrence of `witness` in the conclusion should be abstracted;
    otherwise call EXISTS with an explicit predicate.
    """
    body = th._concl
    avoid = freesl([body, witness])
    if isinstance(witness, Var):
        v = variant(avoid, witness)
    else:
        v = variant(avoid, Var("v", type_of(witness)))
    pred = mk_abs(v, _subst_term(witness, v, body))
    return EXISTS(pred, witness, th)


def CASE_OR(or_thm, left, right):
    h_l, prove_l = left
    h_r, prove_r = right
    branch_l = DISCH(h_l, prove_l(ASSUME(h_l)))
    branch_r = DISCH(h_r, prove_r(ASSUME(h_r)))
    return DISJ_CASES(or_thm, branch_l, branch_r)


# ---------------------------------------------------------------------------
# PROVE_HYP -- discharge an assumption via an existing proof.
#
#   asl1 |- h ;  asl2 |- t   =>   asl1 ∪ (asl2 - {h}) |- t.
# ---------------------------------------------------------------------------

def PROVE_HYP(h_th, th):
    return EQ_MP(DEDUCT_ANTISYM_RULE(h_th, th), h_th)


# ---------------------------------------------------------------------------
# ELIM_EX -- existential elimination via SELECT_AX.
#
#   pred_in : Abs(v, body_v)        # the existential's predicate \v. body_v
#   hyp_ex  : term                  # `?v. body_v`  (a hypothesis term)
#   body_fn : function taking `|- body_v[w/v]` (with w = @pred_in) and
#             returning `|- target` (perhaps with extra hypotheses).
#   Result: ({hyp_ex} ∪ extras) |- target.
# ---------------------------------------------------------------------------

def ELIM_EX(pred_in, hyp_ex, body_fn):
    if not isinstance(pred_in, Abs):
        raise HolError("ELIM_EX: pred_in must be an Abs")
    v_var = pred_in.bvar
    w_t = mk_select(v_var, pred_in.body)           # @v. body_v
    sel_inst = INST_TYPE([(v_var.ty, aty)], SELECT_AX)
    sel_pq = SPEC(v_var, SPEC(pred_in, sel_inst))   # |- pred v ==> pred (@pred)

    pred_v = mk_comb(pred_in, v_var)
    pred_at_w = mk_comb(pred_in, w_t)
    body_v = rand(BETA_CONV(pred_v)._concl)         # = body_v
    body_at_w = rand(BETA_CONV(pred_at_w)._concl)   # = body_v[w/v]

    th_assume_body = EQ_MP(SYM(BETA_CONV(pred_v)), ASSUME(body_v))   # {body_v} |- pred v
    th_pred_at_w   = MP(sel_pq, th_assume_body)                       # {body_v} |- pred (@pred)
    th_body_at_w   = EQ_MP(BETA_CONV(pred_at_w), th_pred_at_w)         # {body_v} |- body_v[w/v]
    body_imp = DISCH(body_v, th_body_at_w)                            # |- body_v ==> body_v[w/v]
    body_imp_gen = GEN(v_var, body_imp)                                # |- !v. body_v ==> body_v[w/v]

    edef = INST_TYPE([(v_var.ty, aty)], EXISTS_DEF)
    eq1 = AP_THM(edef, pred_in)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    th_hyp_unfold = EQ_MP(eq2, ASSUME(hyp_ex))                # {hyp_ex} |- !r. (!v. P v ==> r) ==> r
    th_spec_r = SPEC(body_at_w, th_hyp_unfold)                # {hyp_ex} |- (!v. P v ==> body_at_w) ==> body_at_w
    bridge = BETA_CONV(pred_v)                                 # |- P v = body_v
    spec_body_imp = SPEC(v_var, body_imp_gen)                  # |- body_v ==> body_at_w
    p_v_to_body_at_w = DISCH(pred_v,
                             MP(spec_body_imp, EQ_MP(bridge, ASSUME(pred_v))))
    th_forall_pv_imp = GEN(v_var, p_v_to_body_at_w)
    th_body_at_w_under_hyp = MP(th_spec_r, th_forall_pv_imp)   # {hyp_ex} |- body_at_w

    th_target_under_body_at_w = body_fn(ASSUME(body_at_w))      # {body_at_w, ...} |- target
    return PROVE_HYP(th_body_at_w_under_hyp, th_target_under_body_at_w)


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
# Higher-level tactics: rewriting and AC normalization.
#
# A "rule" is any theorem of the form  |- !v1...vn. lhs = rhs  (outer foralls
# are stripped; the freed vars become pattern variables).  Theorems with no
# outer forall are usable too: their free vars act as literal pattern atoms,
# which lets you pass an induction hypothesis as a rewrite directly.
#
# First-order matching only.  Lambdas in patterns must alpha-match exactly.
# ---------------------------------------------------------------------------

def BETA_RULE(th):
    """Beta-normalize the conclusion of th.  If the conclusion is already in
    beta normal form, returns th unchanged."""
    eq = BETA_NORM(th._concl)
    lhs, rhs = dest_eq(eq._concl)
    return th if aconv(lhs, rhs) else EQ_MP(eq, th)


def _strip_forall(th):
    """Strip outer (!v. ...) layers from th, returning (vars, th_body)."""
    vs = []
    while True:
        c = th._concl
        if (isinstance(c, Comb) and isinstance(c.fun, Const)
                and c.fun.name == "!" and isinstance(c.arg, Abs)):
            v = c.arg.bvar
            th = SPEC(v, th)
            vs.append(v)
        else:
            break
    return vs, th


def _prepare_rule(th):
    """Strip foralls, extract LHS/RHS.  Returns (vars, lhs, rhs, eq_th) or None."""
    vs, body = _strip_forall(th)
    try:
        lhs, rhs = dest_eq(body._concl)
    except Exception:
        return None
    return vs, lhs, rhs, body


def _term_match(pat, tgt, vars_set, subst):
    """First-order match of pat against tgt.
       pat-vars in vars_set are match variables; others must match literally.
       Returns extended subst dict, or None on failure."""
    if isinstance(pat, Var) and pat in vars_set:
        if pat in subst:
            return subst if aconv(subst[pat], tgt) else None
        if type_of(pat) != type_of(tgt):
            return None
        s = dict(subst); s[pat] = tgt
        return s
    if isinstance(pat, Var) and isinstance(tgt, Var):
        return subst if (pat.name == tgt.name and pat.ty == tgt.ty) else None
    if isinstance(pat, Const) and isinstance(tgt, Const):
        return subst if (pat.name == tgt.name and pat.ty == tgt.ty) else None
    if isinstance(pat, Comb) and isinstance(tgt, Comb):
        s = _term_match(pat.fun, tgt.fun, vars_set, subst)
        if s is None: return None
        return _term_match(pat.arg, tgt.arg, vars_set, s)
    if isinstance(pat, Abs) and isinstance(tgt, Abs):
        if pat.bvar.name == tgt.bvar.name and pat.bvar.ty == tgt.bvar.ty:
            return _term_match(pat.body, tgt.body, vars_set, subst)
        return None
    return None


def _try_rules_at(rules, tm):
    """Try each rule at the root of tm.  Returns |- tm = tm' or None."""
    for vs, lhs, rhs, body in rules:
        subst = _term_match(lhs, tm, set(vs), {})
        if subst is None:
            continue
        pairs = [(subst[v], v) for v in vs if v in subst]
        return INST(pairs, body) if pairs else body
    return None


def _bottom_up(rules, tm, under_binder=False):
    """One bottom-up pass: rewrite children once, then iterate rules at the root
       (without descending into the new RHS — that's what the outer fixpoint loop
       in REWRITE_CONV is for).  Returns |- tm = tm' or None if unchanged.

       Inside an Abs body, only rules with empty assumptions are considered:
       hypothetical local facts (e.g. ``ASSUME``-derived equations) routinely
       have RHS terms that re-introduce their own LHS under a binder, which
       would loop.  Closed rewrite rules are safe."""
    active = [r for r in rules if not r[3]._asl] if under_binder else rules

    if isinstance(tm, Comb):
        l_step = _bottom_up(rules, tm.fun, under_binder)
        r_step = _bottom_up(rules, tm.arg, under_binder)
        if l_step is None and r_step is None:
            inner = REFL(tm)
            inner_changed = False
        else:
            l_eq = l_step if l_step is not None else REFL(tm.fun)
            r_eq = r_step if r_step is not None else REFL(tm.arg)
            inner = MK_COMB(l_eq, r_eq)
            inner_changed = True
    elif isinstance(tm, Abs):
        body_step = _bottom_up(rules, tm.body, under_binder=True)
        if body_step is None:
            inner = REFL(tm)
            inner_changed = False
        else:
            # ABS lifts |- s = t to |- (\v. s) = (\v. t) provided v isn't free
            # in the equation's hypotheses.  Active rules under a binder are
            # filtered to empty-asl ones, so this normally succeeds; bail
            # safely otherwise.
            try:
                inner = ABS(tm.bvar, body_step)
                inner_changed = True
            except HolError:
                inner = REFL(tm)
                inner_changed = False
    else:
        inner = REFL(tm)
        inner_changed = False

    for _ in range(256):
        cur = rand(inner._concl)
        root_step = _try_rules_at(active, cur)
        if root_step is None:
            break
        inner = TRANS(inner, root_step)
        inner_changed = True
    else:
        raise HolError("REWRITE: root rule fired 256 times — likely non-terminating")

    return inner if inner_changed else None


def REWRITE_CONV(rules_thms, tm, max_passes=64):
    """Rewrite tm with the given equation theorems to fixpoint, bottom-up.
       Raises HolError if no fixpoint reached after max_passes outer passes
       (likely a non-terminating rule set)."""
    rules = [r for r in (_prepare_rule(t) for t in rules_thms) if r is not None]
    if not rules:
        return REFL(tm)
    th = REFL(tm)
    for _ in range(max_passes):
        cur = rand(th._concl)
        step = _bottom_up(rules, cur)
        if step is None:
            return th
        th = TRANS(th, step)
    raise HolError(f"REWRITE_CONV: did not reach fixpoint in {max_passes} passes "
                   "(rules likely non-terminating)")


def REWRITE_RULE(rules_thms, th):
    """Rewrite th's conclusion with the given equation theorems."""
    eq = REWRITE_CONV(rules_thms, th._concl)
    lhs, rhs = dest_eq(eq._concl)
    return th if aconv(lhs, rhs) else EQ_MP(eq, th)


def REWRITE_PROVE(rules_thms, target_eq):
    """Prove target_eq (= mk_eq(lhs, rhs)) by reducing both sides to a common
       normal form under the rewrite rules."""
    lhs, rhs = dest_eq(target_eq)
    eq_l = REWRITE_CONV(rules_thms, lhs)
    eq_r = REWRITE_CONV(rules_thms, rhs)
    nl, nr = rand(eq_l._concl), rand(eq_r._concl)
    if not aconv(nl, nr):
        raise HolError(
            "REWRITE_PROVE: normal forms differ\n"
            f"  LHS reduces to: {nl}\n"
            f"  RHS reduces to: {nr}"
        )
    return TRANS(eq_l, SYM(eq_r))


# ---------------------------------------------------------------------------
# AC normalization: flatten an AC operator, canonical-sort the leaves, emit
# a kernel proof showing the original equals the sorted form.
# ---------------------------------------------------------------------------

def _term_key(tm):
    """Stable structural ordering on terms (used to canonical-sort AC leaves)."""
    if isinstance(tm, Var):
        return (0, tm.name, str(tm.ty))
    if isinstance(tm, Const):
        return (1, tm.name, str(tm.ty))
    if isinstance(tm, Comb):
        return (2, _term_key(tm.fun), _term_key(tm.arg))
    if isinstance(tm, Abs):
        return (3, tm.bvar.name, str(tm.bvar.ty), _term_key(tm.body))
    return (4, str(tm))


def _is_op_app(op_const, tm):
    """True iff tm = op a b for the given op_const."""
    return (isinstance(tm, Comb) and isinstance(tm.fun, Comb)
            and tm.fun.fun == op_const)


def _right_assoc_conv(op_const, assoc_thm, tm):
    """ |- tm = right_assoc(tm).   Repeatedly applies assoc_thm L→R at the root
        whenever the LHS of the root op is itself an op-application."""
    if not _is_op_app(op_const, tm):
        return REFL(tm)
    left, right = tm.fun.arg, tm.arg
    if not _is_op_app(op_const, left):
        return AP_TERM(mk_comb(op_const, left),
                       _right_assoc_conv(op_const, assoc_thm, right))
    a, b = left.fun.arg, left.arg
    step = SPEC(right, SPEC(b, SPEC(a, assoc_thm)))
    return TRANS(step, _right_assoc_conv(op_const, assoc_thm, rand(step._concl)))


def _flatten_right_assoc(op_const, tm):
    """List of leaves of a right-associated op-tree, in left-to-right order."""
    leaves = []
    while _is_op_app(op_const, tm):
        leaves.append(tm.fun.arg)
        tm = tm.arg
    leaves.append(tm)
    return leaves


def _build_right_assoc(op_const, leaves):
    """Build right-associated op-tree from a non-empty list of leaves."""
    result = leaves[-1]
    for leaf in reversed(leaves[:-1]):
        result = mk_comb(mk_comb(op_const, leaf), result)
    return result


def _swap_at(op_const, assoc_thm, comm_thm, leaves, idx):
    """ |- right_assoc(leaves) = right_assoc(swap(leaves, idx, idx+1))."""
    a, b = leaves[idx], leaves[idx + 1]
    rest = leaves[idx + 2:]
    if not rest:
        swap_eq = SPEC(b, SPEC(a, comm_thm))
    else:
        rest_term = _build_right_assoc(op_const, rest)
        swap_eq = TRANS_CHAIN([
            SYM(SPEC(rest_term, SPEC(b, SPEC(a, assoc_thm)))),
            AP_THM(AP_TERM(op_const, SPEC(b, SPEC(a, comm_thm))), rest_term),
            SPEC(rest_term, SPEC(a, SPEC(b, assoc_thm))),
        ])
    for leaf in reversed(leaves[:idx]):
        swap_eq = AP_TERM(mk_comb(op_const, leaf), swap_eq)
    return swap_eq


def _selection_sort_proof(op_const, assoc_thm, comm_thm, leaves):
    """ |- right_assoc(leaves) = right_assoc(sorted_leaves)."""
    cur = list(leaves)
    eq = REFL(_build_right_assoc(op_const, cur))
    n = len(cur)
    for i in range(n - 1):
        min_idx = i
        for j in range(i + 1, n):
            if _term_key(cur[j]) < _term_key(cur[min_idx]):
                min_idx = j
        while min_idx > i:
            eq = TRANS(eq, _swap_at(op_const, assoc_thm, comm_thm, cur, min_idx - 1))
            cur[min_idx - 1], cur[min_idx] = cur[min_idx], cur[min_idx - 1]
            min_idx -= 1
    return eq


def AC_NORM(op_const, assoc_thm, comm_thm, tm):
    """Returns |- tm = canonical(tm) under AC of op_const.
       assoc_thm: |- !x y z. op (op x y) z = op x (op y z)
       comm_thm:  |- !x y. op x y = op y x"""
    eq1 = _right_assoc_conv(op_const, assoc_thm, tm)
    rhs1 = rand(eq1._concl)
    leaves = _flatten_right_assoc(op_const, rhs1)
    if len(leaves) <= 1:
        return eq1
    eq2 = _selection_sort_proof(op_const, assoc_thm, comm_thm, leaves)
    return TRANS(eq1, eq2)


def AC_PROVE(op_const, assoc_thm, comm_thm, target_eq):
    """Prove `lhs = rhs` by AC-normalizing both sides under op_const."""
    lhs, rhs = dest_eq(target_eq)
    eq_l = AC_NORM(op_const, assoc_thm, comm_thm, lhs)
    eq_r = AC_NORM(op_const, assoc_thm, comm_thm, rhs)
    nl, nr = rand(eq_l._concl), rand(eq_r._concl)
    if not aconv(nl, nr):
        raise HolError(
            "AC_PROVE: AC normal forms differ\n"
            f"  LHS canonical: {nl}\n"
            f"  RHS canonical: {nr}"
        )
    return TRANS(eq_l, SYM(eq_r))


def REWRITE_AC_PROVE(rules, op_const, assoc_thm, comm_thm, target_eq, *, ac_rules=()):
    """Combined: reduce both sides under `rules`, optionally a second pass with
       `ac_rules` (e.g. SUC→+1 to canonicalize before AC), then close with AC.
       Falls back to TRANS+SYM if normal forms already match exactly."""
    lhs, rhs = dest_eq(target_eq)
    eq_l = REWRITE_CONV(rules, lhs)
    eq_r = REWRITE_CONV(rules, rhs)
    if ac_rules:
        eq_l = TRANS(eq_l, REWRITE_CONV(ac_rules, rand(eq_l._concl)))
        eq_r = TRANS(eq_r, REWRITE_CONV(ac_rules, rand(eq_r._concl)))
    nl, nr = rand(eq_l._concl), rand(eq_r._concl)
    if aconv(nl, nr):
        return TRANS(eq_l, SYM(eq_r))
    eq_ac = AC_PROVE(op_const, assoc_thm, comm_thm, mk_eq(nl, nr))
    return TRANS(eq_l, TRANS(eq_ac, SYM(eq_r)))


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


if __name__ == "__main__":
    _selftest()
    print("tactics.py self-tests passed.")
