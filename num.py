"""Peano signature and induction.

Introduces the natural-number type `num`, the constants `1` and `SUC`,
admits Peano's axioms 3-5 (distinctness of successors, injectivity, induction),
and provides the convenience rule `INDUCT` that packages Axiom 5 for
Landau-style proofs.

Primitive recursion (`num_RECURSION`) is the natural next inhabitant of this
module: once it is proved here, addition and multiplication can be introduced
in `nat.py` via specification rather than admitted as axioms.
"""

from fusion import (
    Var, Abs, Comb,
    aty, bool_ty, mk_abs, mk_comb, mk_const, mk_eq, mk_fun_ty,
    mk_type, new_axiom, new_constant, new_type,
    rator, rand, dest_eq, type_of,
    REFL, TRANS, MK_COMB, ASSUME, EQ_MP, INST, INST_TYPE, HolError,
)
from axioms import (
    SELECT_AX,
    mk_and, mk_imp, mk_forall, mk_exists, mk_not,
)
from logic import (
    AP_TERM, AP_THM, BETA_CONV, SYM, SPEC, GEN,
    CONJ, CONJUNCT1, CONJUNCT2, DISCH, MP, EXISTS,
    PROVE_HYP, ELIM_EX, NOT_ELIM, CONTR,
)


# ---------------------------------------------------------------------------
# num signature.
# ---------------------------------------------------------------------------

new_type("num", 0)
num_ty = mk_type("num", [])

new_constant("1", num_ty)
ONE = mk_const("1", [])

new_constant("SUC", mk_fun_ty(num_ty, num_ty))
SUC = mk_const("SUC", [])

def mk_suc(t):
    return mk_comb(SUC, t)


# Standard variable names re-used throughout the arithmetic development.
x = Var("x", num_ty)
y = Var("y", num_ty)
z = Var("z", num_ty)
u = Var("u", num_ty)
v = Var("v", num_ty)
w = Var("w", num_ty)
P = Var("P", mk_fun_ty(num_ty, bool_ty))


# ---------------------------------------------------------------------------
# Peano Axioms 3, 4, 5.
# ---------------------------------------------------------------------------

# Axiom 3:   |- !x. ~(x' = 1)
AXIOM_3 = new_axiom(mk_forall(x, mk_not(mk_eq(mk_suc(x), ONE))))

# Axiom 4:   |- !x y. x' = y' ==> x = y
AXIOM_4 = new_axiom(
    mk_forall(x, mk_forall(y,
        mk_imp(mk_eq(mk_suc(x), mk_suc(y)),
               mk_eq(x, y)))))

# Axiom 5 (induction):
#   |- !P. P 1 /\ (!x. P x ==> P (x')) ==> !x. P x
INDUCTION = new_axiom(
    mk_forall(P,
        mk_imp(
            mk_and(mk_comb(P, ONE),
                   mk_forall(x, mk_imp(mk_comb(P, x),
                                       mk_comb(P, mk_suc(x))))),
            mk_forall(x, mk_comb(P, x)))))


# ---------------------------------------------------------------------------
# Induction helper -- packages Axiom 5 for Landau-style proofs.
#
# Given a predicate  pred = \v. body[v]  and theorems
#       base_th : |- body[1/v]
#       step_th : |- !v. body[v] ==> body[v'/v]
# returns           |- !v. body[v].
# ---------------------------------------------------------------------------

def INDUCT(pred, base_th, step_th):
    if not isinstance(pred, Abs):
        raise HolError("INDUCT: pred must be an Abs")
    v_var = pred.bvar
    pred_1  = mk_comb(pred, ONE)
    pred_v  = mk_comb(pred, v_var)
    pred_vs = mk_comb(pred, mk_suc(v_var))
    base_pred = EQ_MP(SYM(BETA_CONV(pred_1)), base_th)
    inst_step    = SPEC(v_var, step_th)
    body_assume  = EQ_MP(BETA_CONV(pred_v), ASSUME(pred_v))
    body_succ    = MP(inst_step, body_assume)
    pred_vs_th   = EQ_MP(SYM(BETA_CONV(pred_vs)), body_succ)
    step_pred    = GEN(v_var, DISCH(pred_v, pred_vs_th))
    ind_inst     = SPEC(pred, INDUCTION)
    forall_pred  = MP(ind_inst, CONJ(base_pred, step_pred))
    body_th = EQ_MP(BETA_CONV(pred_v), SPEC(v_var, forall_pred))
    return GEN(v_var, body_th)


# ---------------------------------------------------------------------------
# Primitive recursion theorem.
#
#   |- !c:A h:num->A->A. ?fn:num->A. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
#
# Strategy: define the inductive graph
#     R c h n m  :=  !Q. (Q 1 c /\ (!k a. Q k a ==> Q (SUC k) (h k a))) ==> Q n m
# and prove by induction on n that  ?!m. R c h n m.  Then  fn := \n. @m. R c h n m
# satisfies the recursion equations.
# ---------------------------------------------------------------------------

# Standard variable names used in the recursion proof (live at type variable A
# so the final theorem is polymorphic).
_A = aty
_num_to_A     = mk_fun_ty(num_ty, _A)
_A_to_A       = mk_fun_ty(_A, _A)
_h_ty         = mk_fun_ty(num_ty, _A_to_A)
_Q_ty         = mk_fun_ty(num_ty, mk_fun_ty(_A, bool_ty))

_c   = Var("c", _A)
_h   = Var("h", _h_ty)
_n   = Var("n", num_ty)
_k   = Var("k", num_ty)
_m   = Var("m", _A)
_a   = Var("a", _A)
_b   = Var("b", _A)
_m1  = Var("m1", _A)
_m2  = Var("m2", _A)
_Q   = Var("Q", _Q_ty)
_fn  = Var("fn", _num_to_A)


def _mk_closure_hyp(Q_term, c_term, h_term):
    """Build the term  Q 1 c /\\ (!k a. Q k a ==> Q (SUC k) (h k a))."""
    Q_1_c   = mk_comb(mk_comb(Q_term, ONE), c_term)
    h_k_a   = mk_comb(mk_comb(h_term, _k), _a)
    Q_k_a   = mk_comb(mk_comb(Q_term, _k), _a)
    Q_sk_h  = mk_comb(mk_comb(Q_term, mk_suc(_k)), h_k_a)
    closure = mk_forall(_k, mk_forall(_a, mk_imp(Q_k_a, Q_sk_h)))
    return mk_and(Q_1_c, closure)


def _mk_R(c_term, h_term, n_term, m_term):
    """Build R c h n m as  !Q. (Q 1 c /\\ closure) ==> Q n m."""
    hyp = _mk_closure_hyp(_Q, c_term, h_term)
    Q_n_m = mk_comb(mk_comb(_Q, n_term), m_term)
    return mk_forall(_Q, mk_imp(hyp, Q_n_m))


def _prove_R_at_1():
    """ |- R c h 1 c    (with c, h as free variables). """
    hyp = _mk_closure_hyp(_Q, _c, _h)
    h_th = ASSUME(hyp)                            # {hyp} |- hyp
    Q_1_c = CONJUNCT1(h_th)                       # {hyp} |- Q 1 c
    return GEN(_Q, DISCH(hyp, Q_1_c))             # |- !Q. hyp ==> Q 1 c

R_AT_1 = _prove_R_at_1()


def _prove_R_step():
    """ |- !n m. R c h n m ==> R c h (SUC n) (h n m). """
    R_n_m = _mk_R(_c, _h, _n, _m)
    h_n_m = mk_comb(mk_comb(_h, _n), _m)
    hyp = _mk_closure_hyp(_Q, _c, _h)

    th_R = ASSUME(R_n_m)                          # {R} |- R c h n m
    th_hyp = ASSUME(hyp)                          # {hyp} |- Q 1 c /\ closure
    R_at_Q = SPEC(_Q, th_R)                       # {R} |- hyp ==> Q n m
    Q_n_m = MP(R_at_Q, th_hyp)                    # {R, hyp} |- Q n m

    closure_th = CONJUNCT2(th_hyp)                # {hyp} |- !k a. Q k a ==> Q (SUC k) (h k a)
    closure_at_nm = SPEC(_m, SPEC(_n, closure_th))   # {hyp} |- Q n m ==> Q (SUC n) (h n m)
    Q_sn = MP(closure_at_nm, Q_n_m)               # {R, hyp} |- Q (SUC n) (h n m)

    inner = GEN(_Q, DISCH(hyp, Q_sn))             # {R} |- R c h (SUC n) (h n m)
    return GEN(_n, GEN(_m, DISCH(R_n_m, inner)))

R_STEP = _prove_R_step()


def _mk_unique_at(n_term):
    """Build  (?m. R c h n m) /\\ (!m1 m2. R c h n m1 /\\ R c h n m2 ==> m1 = m2)."""
    R_n_m  = _mk_R(_c, _h, n_term, _m)
    R_n_m1 = _mk_R(_c, _h, n_term, _m1)
    R_n_m2 = _mk_R(_c, _h, n_term, _m2)
    exist  = mk_exists(_m, R_n_m)
    unique = mk_forall(_m1, mk_forall(_m2,
                mk_imp(mk_and(R_n_m1, R_n_m2), mk_eq(_m1, _m2))))
    return mk_and(exist, unique)


def _prove_R_unique_base():
    """ |- (?m. R c h 1 m) /\\ (!m1 m2. R c h 1 m1 /\\ R c h 1 m2 ==> m1 = m2). """
    R_1_m   = _mk_R(_c, _h, ONE, _m)
    R_1_m1  = _mk_R(_c, _h, ONE, _m1)
    R_1_m2  = _mk_R(_c, _h, ONE, _m2)

    # Existence: witness m = c, using Lemma 1.
    exist_th = EXISTS(mk_abs(_m, R_1_m), _c, R_AT_1)   # |- ?m. R c h 1 m

    # Uniqueness: define Q'(k, a) := (k = 1) ==> (a = c).
    # We will show Q' satisfies the closure hypothesis, then specialise R c h 1 _ at Q'.
    Qp_body = mk_imp(mk_eq(_k, ONE), mk_eq(_a, _c))     # using free k, a; but Q' has type num->A->bool
    # Actually the bound vars in Q' are independent: Q' = \k:num. \a:A. (k = 1) ==> (a = c)
    k_b = Var("k", num_ty)
    a_b = Var("a", _A)
    Qp = mk_abs(k_b, mk_abs(a_b, mk_imp(mk_eq(k_b, ONE), mk_eq(a_b, _c))))

    def apply_Qp(k_t, a_t):
        """Return (|- Q' k a = (k = 1 ==> a = c), the equality from beta)."""
        # Q' k a beta-reduces to (k = 1) ==> (a = c).
        Qp_k = mk_comb(Qp, k_t)
        bot1 = BETA_CONV(Qp_k)                   # |- Q' k = \a. ...
        Qp_k_a = mk_comb(Qp_k, a_t)
        bot2 = AP_THM(bot1, a_t)                 # |- Q' k a = (\a. ...) a
        bot3 = TRANS(bot2, BETA_CONV(rand(bot2._concl)))
        return bot3                              # |- Q' k a = (k = 1 ==> a = c)

    # 1. Q' 1 c.   reduces to (1 = 1) ==> (c = c), proved by DISCH+REFL.
    eq_red_1c = apply_Qp(ONE, _c)
    inner_1c = DISCH(mk_eq(ONE, ONE), REFL(_c))   # |- (1 = 1) ==> (c = c)
    Qp_1_c = EQ_MP(SYM(eq_red_1c), inner_1c)      # |- Q' 1 c

    # 2. !k a. Q' k a ==> Q' (SUC k) (h k a).   Body: SUC k = 1 ==> h k a = c.
    # Vacuous: SUC k != 1 by AXIOM_3, so the hypothesis SUC k = 1 leads to F, hence anything.
    h_k_a = mk_comb(mk_comb(_h, _k), _a)
    eq_red_LHS = apply_Qp(_k, _a)                          # |- Q' k a = (k=1 ==> a=c)
    eq_red_RHS = apply_Qp(mk_suc(_k), h_k_a)               # |- Q' (SUC k) (h k a) = (SUC k=1 ==> h k a=c)
    # Inner: SUC k = 1 ==> h k a = c.   Use AXIOM_3 specialized to k.
    ax3_k = SPEC(_k, AXIOM_3)                              # |- ~(SUC k = 1)
    # NOT_ELIM gives  |- (SUC k = 1) ==> F.
    from logic import NOT_ELIM, CONTR
    sk_eq_1_imp_F = NOT_ELIM(ax3_k)                        # |- (SUC k = 1) ==> F
    # |- (SUC k = 1) ==> (h k a = c):  apply CONTR.
    h_sk_eq_1 = ASSUME(mk_eq(mk_suc(_k), ONE))             # {SUC k = 1} |- SUC k = 1
    th_F = MP(sk_eq_1_imp_F, h_sk_eq_1)                    # {SUC k = 1} |- F
    th_hkc = CONTR(mk_eq(h_k_a, _c), th_F)                 # {SUC k = 1} |- h k a = c
    inner_step = DISCH(mk_eq(mk_suc(_k), ONE), th_hkc)     # |- (SUC k = 1) ==> (h k a = c)
    # Lift through eq_red_RHS:
    Qp_sk_hka = EQ_MP(SYM(eq_red_RHS), inner_step)         # |- Q' (SUC k) (h k a)
    # Build  Q' k a ==> Q' (SUC k) (h k a):  the antecedent is ignored (RHS holds).
    Qp_k_a_term = rand(eq_red_LHS._concl).fun.arg   # not actually needed, but for clarity
    Qp_k_a_term = mk_comb(mk_comb(Qp, _k), _a)
    step_imp = DISCH(Qp_k_a_term, Qp_sk_hka)               # |- Q' k a ==> Q' (SUC k) (h k a)
    closure_Qp = GEN(_k, GEN(_a, step_imp))                # |- !k a. Q' k a ==> Q' (SUC k) (h k a)

    closure_hyp_Qp = CONJ(Qp_1_c, closure_Qp)              # |- (Q' 1 c) /\ closure(Q')

    # Now derive uniqueness:  R c h 1 m1 /\ R c h 1 m2 ==> m1 = m2.
    h_R_m1 = ASSUME(R_1_m1)                                # {R 1 m1} |- ...
    h_R_m2 = ASSUME(R_1_m2)
    R_at_Qp_m1 = SPEC(Qp, h_R_m1)                          # {R 1 m1} |- (Q' 1 c /\ closure) ==> Q' 1 m1
    Qp_1_m1 = MP(R_at_Qp_m1, closure_hyp_Qp)               # {R 1 m1} |- Q' 1 m1
    # Convert via  Q' 1 m1 = ((1 = 1) ==> (m1 = c)).
    eq_red_1m1 = apply_Qp(ONE, _m1)
    inner_1m1 = EQ_MP(eq_red_1m1, Qp_1_m1)                 # {R 1 m1} |- (1=1) ==> (m1 = c)
    m1_eq_c = MP(inner_1m1, REFL(ONE))                     # {R 1 m1} |- m1 = c
    # Same for m2.
    R_at_Qp_m2 = SPEC(Qp, h_R_m2)
    Qp_1_m2 = MP(R_at_Qp_m2, closure_hyp_Qp)
    eq_red_1m2 = apply_Qp(ONE, _m2)
    inner_1m2 = EQ_MP(eq_red_1m2, Qp_1_m2)
    m2_eq_c = MP(inner_1m2, REFL(ONE))                     # {R 1 m2} |- m2 = c
    # Combine:  m1 = c = m2.
    m1_eq_m2 = TRANS(m1_eq_c, SYM(m2_eq_c))                # {R 1 m1, R 1 m2} |- m1 = m2

    # Discharge into  (R 1 m1 /\ R 1 m2) ==> m1 = m2.
    conj_h = ASSUME(mk_and(R_1_m1, R_1_m2))
    use_conj = MP(MP(DISCH(R_1_m1, DISCH(R_1_m2, m1_eq_m2)),
                     CONJUNCT1(conj_h)), CONJUNCT2(conj_h))
    unique_th = GEN(_m1, GEN(_m2,
                    DISCH(mk_and(R_1_m1, R_1_m2), use_conj)))

    return CONJ(exist_th, unique_th)

R_UNIQUE_BASE = _prove_R_unique_base()


def _prove_R_unique_step():
    """ |- !n. _mk_unique_at(n) ==> _mk_unique_at(SUC n). """
    R_n_m   = _mk_R(_c, _h, _n, _m)
    pred_R_n = mk_abs(_m, R_n_m)             # \m. R c h n m

    IH_term = _mk_unique_at(_n)               # IH at n
    IH = ASSUME(IH_term)
    IH_exist  = CONJUNCT1(IH)                 # {IH} |- ?m. R c h n m
    IH_unique = CONJUNCT2(IH)                 # {IH} |- !m1 m2. R c h n m1 /\ R c h n m2 ==> m1 = m2

    # Witness: m_n = @m. R c h n m.
    sel_const = mk_const("@", [(_A, aty)])
    m_n = mk_comb(sel_const, pred_R_n)        # @m. R c h n m

    # We'll build target := _mk_unique_at(SUC n)  under hypothesis {IH, ...},
    # using ELIM_EX to introduce a hypothesis  R c h n m_n.
    R_n_mn = _mk_R(_c, _h, _n, m_n)           # R c h n m_n

    # ----- Existence at SUC n. -----
    # From R c h n m_n  (hypothesis), R_STEP gives R c h (SUC n) (h n m_n).
    h_n_mn = mk_comb(mk_comb(_h, _n), m_n)
    R_step_inst = SPEC(m_n, SPEC(_n, R_STEP))                 # |- R c h n m_n ==> R c h (SUC n) (h n m_n)
    R_sn_hn = MP(R_step_inst, ASSUME(R_n_mn))                  # {R_n_mn} |- R c h (SUC n) (h n m_n)

    R_sn_m = _mk_R(_c, _h, mk_suc(_n), _m)
    pred_R_sn = mk_abs(_m, R_sn_m)
    exist_sn = EXISTS(pred_R_sn, h_n_mn, R_sn_hn)              # {R_n_mn} |- ?m. R c h (SUC n) m

    # ----- Uniqueness at SUC n. -----
    # Define  Q'(k, b) := R c h k b /\ (k = SUC n ==> b = h n m_n).
    k_b = Var("k", num_ty)
    a_b = Var("a", _A)
    Qp_body = mk_and(_mk_R(_c, _h, k_b, a_b),
                      mk_imp(mk_eq(k_b, mk_suc(_n)),
                             mk_eq(a_b, h_n_mn)))
    Qp = mk_abs(k_b, mk_abs(a_b, Qp_body))

    def apply_Qp(k_t, a_t):
        r"""Return |- Q' k a = (R c h k a /\ (k = SUC n ==> a = h n m_n))."""
        Qp_k = mk_comb(Qp, k_t)
        bot1 = BETA_CONV(Qp_k)                # |- Q' k = \a. ...
        Qp_k_a = mk_comb(Qp_k, a_t)
        bot2 = AP_THM(bot1, a_t)
        bot3 = TRANS(bot2, BETA_CONV(rand(bot2._concl)))
        return bot3                            # |- Q' k a = body[k_t, a_t]

    # 1. Q'(1, c).  We need:
    #    R c h 1 c    /\    (1 = SUC n ==> c = h n m_n).
    Qp_1c_eq = apply_Qp(ONE, _c)               # |- Q' 1 c = (R c h 1 c /\ (1 = SUC n ==> c = h n m_n))
    R_1_c = R_AT_1                              # |- R c h 1 c
    # second conjunct: (1 = SUC n ==> c = h n m_n).  Vacuous via AXIOM_3 (SUC n != 1 i.e. ~(1 = SUC n)? -- direction: AXIOM_3 has SUC n != 1).
    # Assume 1 = SUC n.  SYM gives SUC n = 1.  AXIOM_3 says ~(SUC n = 1).  Contradiction.
    h_1_eq_sn = ASSUME(mk_eq(ONE, mk_suc(_n)))           # {1 = SUC n} |- 1 = SUC n
    sn_eq_1 = SYM(h_1_eq_sn)                              # {1 = SUC n} |- SUC n = 1
    ax3_n = SPEC(_n, AXIOM_3)                             # |- ~(SUC n = 1)
    th_F_1 = MP(NOT_ELIM(ax3_n), sn_eq_1)                  # {1 = SUC n} |- F
    th_c_eq_hnmn = CONTR(mk_eq(_c, h_n_mn), th_F_1)        # {1 = SUC n} |- c = h n m_n
    inner_1c = DISCH(mk_eq(ONE, mk_suc(_n)), th_c_eq_hnmn)   # |- 1 = SUC n ==> c = h n m_n
    Qp_1_c_inner = CONJ(R_1_c, inner_1c)                   # |- R c h 1 c /\ (1 = SUC n ==> c = h n m_n)
    Qp_1_c = EQ_MP(SYM(Qp_1c_eq), Qp_1_c_inner)            # |- Q' 1 c

    # 2. !k a. Q' k a ==> Q' (SUC k) (h k a).
    h_k_a = mk_comb(mk_comb(_h, _k), _a)
    Qp_k_a_eq = apply_Qp(_k, _a)                                  # |- Q' k a = (R c h k a /\ (k = SUC n ==> a = h n m_n))
    Qp_sk_hka_eq = apply_Qp(mk_suc(_k), h_k_a)                    # |- Q' (SUC k) (h k a) = (R c h (SUC k) (h k a) /\ ...)

    # Assume Q' k a.  Get R c h k a and (k = SUC n ==> a = h n m_n).
    Qp_k_a = mk_comb(mk_comb(Qp, _k), _a)
    h_Qp_ka = ASSUME(Qp_k_a)
    inner_Qp = EQ_MP(Qp_k_a_eq, h_Qp_ka)                          # {Qp_k_a} |- R k a /\ (k = SUC n ==> a = h n m_n)
    R_k_a = CONJUNCT1(inner_Qp)                                   # {Qp_k_a} |- R c h k a
    second_part = CONJUNCT2(inner_Qp)                              # {Qp_k_a} |- k = SUC n ==> a = h n m_n

    # First conjunct of Q' (SUC k) (h k a): R c h (SUC k) (h k a).
    R_step_at_ka = SPEC(_a, SPEC(_k, R_STEP))                      # |- R c h k a ==> R c h (SUC k) (h k a)
    R_sk_hka = MP(R_step_at_ka, R_k_a)                              # {Qp_k_a} |- R c h (SUC k) (h k a)

    # Second conjunct: (SUC k = SUC n ==> h k a = h n m_n).
    # Assume SUC k = SUC n. By AXIOM_4, k = n.
    h_sk_eq_sn = ASSUME(mk_eq(mk_suc(_k), mk_suc(_n)))             # {SUC k = SUC n} |- SUC k = SUC n
    ax4_kn = SPEC(_n, SPEC(_k, AXIOM_4))                            # |- SUC k = SUC n ==> k = n
    k_eq_n = MP(ax4_kn, h_sk_eq_sn)                                 # {SUC k = SUC n} |- k = n

    # Now from R_k_a (= R c h k a) plus k = n, get R c h n a (rewrite k to n).
    # AP rewriting: substitute k=n in R c h k a.  Use AP_THM/AP_TERM at the relation level.
    # Easier: use AP_TERM on the function form `\k. R c h k a` applied to k=n.
    # But R c h k a contains k.  Let's do it by congruence:
    #   R c h k a = R c h n a   from k = n.
    # The shape: R c h k a = (!Q. (...) ==> Q k a).  We need to rewrite k inside.
    # Build the abstraction \kk. R c h kk a, then AP_TERM to k_eq_n.
    kk = Var("kk", num_ty)
    R_func_a = mk_abs(kk, _mk_R(_c, _h, kk, _a))                    # \kk. R c h kk a
    # |- (\kk. R c h kk a) k = R c h k a
    beta_at_k = BETA_CONV(mk_comb(R_func_a, _k))
    beta_at_n = BETA_CONV(mk_comb(R_func_a, _n))
    # AP_TERM applied to k_eq_n gives:  |- (\kk. R c h kk a) k = (\kk. R c h kk a) n.
    func_eq = AP_TERM(R_func_a, k_eq_n)                              # {SUC k = SUC n} |- (\kk. R c h kk a) k = (\kk. R c h kk a) n
    # Combine:  R c h k a = (\kk. R k a) k = (\kk. R k a) n = R c h n a.
    R_k_eq_R_n = TRANS(SYM(beta_at_k), TRANS(func_eq, beta_at_n))    # {SUC k = SUC n} |- R c h k a = R c h n a
    R_n_a = EQ_MP(R_k_eq_R_n, R_k_a)                                  # {Qp_k_a, SUC k = SUC n} |- R c h n a

    # Now apply IH_unique at (a, m_n): R c h n a /\ R c h n m_n ==> a = m_n.
    IH_at_a_mn = SPEC(m_n, SPEC(_a, IH_unique))                       # {IH} |- R n a /\ R n m_n ==> a = m_n
    R_n_mn_h = ASSUME(R_n_mn)                                          # {R_n_mn} |- R c h n m_n
    a_eq_mn = MP(IH_at_a_mn, CONJ(R_n_a, R_n_mn_h))                    # {Qp_k_a, SUC k = SUC n, IH, R_n_mn} |- a = m_n

    # Now h k a = h n m_n.  Use AP_TERM/AP_THM on h.
    # h k a = h n a   (from k = n via AP_THM(AP_TERM h k_eq_n) ).
    # Then h n a = h n m_n via AP_TERM(h n) on a_eq_mn.
    h_k_eq_h_n = AP_TERM(_h, k_eq_n)                                   # {SUC k = SUC n} |- h k = h n
    h_k_a_eq_h_n_a = AP_THM(h_k_eq_h_n, _a)                            # {SUC k = SUC n} |- h k a = h n a
    h_n_a_eq_h_n_mn = AP_TERM(mk_comb(_h, _n), a_eq_mn)                # {Qp_k_a, SUC k=SUC n, IH, R_n_mn} |- h n a = h n m_n
    h_k_a_eq_h_n_mn = TRANS(h_k_a_eq_h_n_a, h_n_a_eq_h_n_mn)            # ditto |- h k a = h n m_n

    second_imp_inner = DISCH(mk_eq(mk_suc(_k), mk_suc(_n)), h_k_a_eq_h_n_mn)   # {Qp_k_a, IH, R_n_mn} |- SUC k = SUC n ==> h k a = h n m_n

    Qp_sk_hka_inner = CONJ(R_sk_hka, second_imp_inner)                  # {Qp_k_a, IH, R_n_mn} |- R c h (SUC k) (h k a) /\ (SUC k = SUC n ==> h k a = h n m_n)
    Qp_sk_hka = EQ_MP(SYM(Qp_sk_hka_eq), Qp_sk_hka_inner)               # {...} |- Q' (SUC k) (h k a)

    # Build (Q' k a ==> Q' (SUC k) (h k a)) under {IH, R_n_mn}, then GEN k, a.
    step_imp_Qp = DISCH(Qp_k_a, Qp_sk_hka)                              # {IH, R_n_mn} |- Q' k a ==> Q' (SUC k) (h k a)
    closure_Qp = GEN(_k, GEN(_a, step_imp_Qp))                          # {IH, R_n_mn} |- !k a. Q' k a ==> Q' (SUC k) (h k a)

    closure_hyp_Qp_th = CONJ(Qp_1_c, closure_Qp)                        # {IH, R_n_mn} |- (Q' 1 c) /\ closure(Q')

    # Now assume R c h (SUC n) m1, R c h (SUC n) m2.
    R_sn_m1 = _mk_R(_c, _h, mk_suc(_n), _m1)
    R_sn_m2 = _mk_R(_c, _h, mk_suc(_n), _m2)
    h_R_sn_m1 = ASSUME(R_sn_m1)
    h_R_sn_m2 = ASSUME(R_sn_m2)
    R_at_Qp_m1 = SPEC(Qp, h_R_sn_m1)                                     # {R_sn_m1} |- ((Q' 1 c) /\ closure) ==> Q' (SUC n) m1
    Qp_sn_m1 = MP(R_at_Qp_m1, closure_hyp_Qp_th)                          # {R_sn_m1, IH, R_n_mn} |- Q' (SUC n) m1

    Qp_sn_m1_eq = apply_Qp(mk_suc(_n), _m1)                               # |- Q' (SUC n) m1 = (R (SUC n) m1 /\ (SUC n = SUC n ==> m1 = h n m_n))
    inner_m1 = EQ_MP(Qp_sn_m1_eq, Qp_sn_m1)
    second_m1 = CONJUNCT2(inner_m1)                                       # {...} |- SUC n = SUC n ==> m1 = h n m_n
    m1_eq_hnmn = MP(second_m1, REFL(mk_suc(_n)))                          # {R_sn_m1, IH, R_n_mn} |- m1 = h n m_n

    R_at_Qp_m2 = SPEC(Qp, h_R_sn_m2)
    Qp_sn_m2 = MP(R_at_Qp_m2, closure_hyp_Qp_th)
    Qp_sn_m2_eq = apply_Qp(mk_suc(_n), _m2)
    inner_m2 = EQ_MP(Qp_sn_m2_eq, Qp_sn_m2)
    second_m2 = CONJUNCT2(inner_m2)
    m2_eq_hnmn = MP(second_m2, REFL(mk_suc(_n)))                          # {R_sn_m2, IH, R_n_mn} |- m2 = h n m_n

    m1_eq_m2 = TRANS(m1_eq_hnmn, SYM(m2_eq_hnmn))                          # {R_sn_m1, R_sn_m2, IH, R_n_mn} |- m1 = m2

    # Build  (R_sn_m1 /\ R_sn_m2) ==> m1 = m2:
    conj_h = ASSUME(mk_and(R_sn_m1, R_sn_m2))
    m1_eq_m2_combined = MP(MP(DISCH(R_sn_m1, DISCH(R_sn_m2, m1_eq_m2)),
                                CONJUNCT1(conj_h)),
                            CONJUNCT2(conj_h))
    unique_sn = GEN(_m1, GEN(_m2,
                       DISCH(mk_and(R_sn_m1, R_sn_m2), m1_eq_m2_combined)))
    # unique_sn : {IH, R_n_mn} |- !m1 m2. R c h (SUC n) m1 /\ R c h (SUC n) m2 ==> m1 = m2

    # Combine existence and uniqueness at SUC n.
    combined_sn = CONJ(exist_sn, unique_sn)                                # {IH, R_n_mn} |- _mk_unique_at(SUC n)

    # Now eliminate R_n_mn via ELIM_EX from IH_exist (which is `?m. R c h n m`).
    # Build body_fn such that body_fn(ASSUME(R c h n m_n)) returns combined_sn.
    # The witness via ELIM_EX is `@m. R c h n m` = m_n; so body_v[w/v] = R c h n m_n exactly.
    R_n_pred = pred_R_n   # \m. R c h n m
    # Sanity: BETA_CONV at m_n yields R_n_mn.
    # Also IH_exist is `?m. R c h n m`. So hyp_ex = mk_exists(_m, R_n_m).
    hyp_ex = mk_exists(_m, R_n_m)

    def body_fn(th_R_n_w):
        # th_R_n_w : {R c h n m_n} |- R c h n m_n
        # We want combined_sn but with R_n_mn replaced as a hypothesis.
        # combined_sn already uses ASSUME(R_n_mn), so body_fn(_) effectively is just combined_sn.
        # But we need to replace its ASSUME(R_n_mn) hypothesis with th_R_n_w.
        # PROVE_HYP(th_R_n_w, combined_sn) does this.
        return PROVE_HYP(th_R_n_w, combined_sn)

    # ELIM_EX wraps everything: returns {hyp_ex} ∪ ... |- target.
    combined_under_IH = ELIM_EX(R_n_pred, hyp_ex, body_fn)                  # {hyp_ex, IH} |- combined_sn

    # hyp_ex is exactly IH_exist's conclusion. Discharge it via PROVE_HYP using IH_exist.
    combined_final = PROVE_HYP(IH_exist, combined_under_IH)                  # {IH} |- combined_sn

    return GEN(_n, DISCH(IH_term, combined_final))


R_UNIQUE_STEP = _prove_R_unique_step()


# Now combine via INDUCT to get R_UNIQUE: |- !n. _mk_unique_at(n).
def _prove_R_unique():
    pred = mk_abs(_n, _mk_unique_at(_n))
    return INDUCT(pred, R_UNIQUE_BASE, R_UNIQUE_STEP)

R_UNIQUE = _prove_R_unique()


# ---------------------------------------------------------------------------
# NUM_RECURSION:  |- !c h. ?fn:num->A. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
# ---------------------------------------------------------------------------

def _prove_num_recursion():
    # Define fn := \n. @m. R c h n m.
    # So fn 1 = @m. R c h 1 m.
    # Show fn 1 = c via uniqueness at 1.
    # And fn (SUC n) = h n (fn n) via uniqueness at SUC n combined with R_STEP.
    R_n_m   = _mk_R(_c, _h, _n, _m)
    R_1_m   = _mk_R(_c, _h, ONE, _m)
    pred_R_n = mk_abs(_m, R_n_m)
    pred_R_1 = mk_abs(_m, R_1_m)
    sel_const = mk_const("@", [(_A, aty)])
    fn_body = mk_abs(_n, mk_comb(sel_const, pred_R_n))   # \n. @m. R c h n m

    # fn applied to a term k beta-reduces to @m. R c h k m.
    # Define convenience:
    def fn_app(k_t):
        return mk_comb(fn_body, k_t)

    # Step 1: fn 1 = c.
    # fn 1 beta-reduces to @m. R c h 1 m.
    # By R_UNIQUE specialised at 1, ?m. R c h 1 m  AND uniqueness.
    # Both R_AT_1 and SELECT_AX give R c h 1 (@m. R c h 1 m). Then uniqueness with R_AT_1 gives @m... = c.
    R_unique_1 = SPEC(ONE, R_UNIQUE)                                    # |- ?m. R 1 m /\ uniqueness at 1
    exist_1  = CONJUNCT1(R_unique_1)                                     # |- ?m. R c h 1 m
    unique_1 = CONJUNCT2(R_unique_1)                                     # |- !m1 m2. R 1 m1 /\ R 1 m2 ==> m1 = m2

    # Use SELECT_AX to derive R c h 1 (@m. R 1 m).
    # SELECT_AX: !P x. P x ==> P (@P).
    sel_inst = INST_TYPE([(_A, aty)], SELECT_AX)
    sel_at_pred1 = SPEC(_m, SPEC(pred_R_1, sel_inst))                    # |- pred_R_1 m ==> pred_R_1 (@pred_R_1)
    # Convert to R 1 m ==> R 1 (@pred_R_1) via BETA.
    pred_R_1_at_m = mk_comb(pred_R_1, _m)
    pred_R_1_at_w = mk_comb(pred_R_1, mk_comb(sel_const, pred_R_1))
    body_v = rand(BETA_CONV(pred_R_1_at_m)._concl)   # = R c h 1 m  (with _m free)
    body_at_w = rand(BETA_CONV(pred_R_1_at_w)._concl)  # = R c h 1 (@m. R 1 m)
    th_pred_v = EQ_MP(SYM(BETA_CONV(pred_R_1_at_m)), ASSUME(body_v))     # {body_v} |- pred_R_1 m
    th_pred_w = MP(sel_at_pred1, th_pred_v)                                # {body_v} |- pred_R_1 (@..)
    th_body_at_w = EQ_MP(BETA_CONV(pred_R_1_at_w), th_pred_w)              # {body_v} |- R 1 (@..)

    # Now using ELIM_EX with hyp_ex = exist_1 conclusion to get {exist_1.concl} |- R c h 1 (@m. R 1 m).
    ex_term_1 = exist_1._concl

    def body_fn_1(th):
        # th : {R 1 m_1} |- R 1 m_1 where m_1 = @m. R 1 m and th is body_at_w
        return th
    th_R_1_atP = ELIM_EX(pred_R_1, ex_term_1, body_fn_1)                  # {ex_term_1} |- R c h 1 (@m. R 1 m)
    th_R_1_atP_clean = PROVE_HYP(exist_1, th_R_1_atP)                      # |- R c h 1 (@m. R 1 m)

    # R_AT_1: |- R c h 1 c.  Together with uniqueness at 1, conclude (@m. R 1 m) = c.
    sel_pred_R_1 = mk_comb(sel_const, pred_R_1)                            # @m. R c h 1 m
    unique_at_w_c = SPEC(_c, SPEC(sel_pred_R_1, unique_1))                  # |- R 1 (@..) /\ R 1 c ==> (@..) = c
    sel_eq_c = MP(unique_at_w_c, CONJ(th_R_1_atP_clean, R_AT_1))            # |- (@..) = c

    # fn 1 = (\n. @m. R n m) 1 = @m. R 1 m  via BETA.
    fn_1 = fn_app(ONE)
    beta_fn_1 = BETA_CONV(fn_1)                                              # |- fn 1 = @m. R 1 m
    fn_1_eq_c = TRANS(beta_fn_1, sel_eq_c)                                   # |- fn 1 = c

    # Step 2: !n. fn (SUC n) = h n (fn n).
    # By same trick, we get  R c h k (@m. R c h k m)  for any k (as long as ?m. R c h k m).
    # Specialising R_UNIQUE at _n we get existence and uniqueness at n.
    R_unique_n = SPEC(_n, R_UNIQUE)
    exist_n  = CONJUNCT1(R_unique_n)                                          # |- ?m. R c h n m
    R_unique_sn = SPEC(mk_suc(_n), R_UNIQUE)
    unique_sn = CONJUNCT2(R_unique_sn)                                         # |- !m1 m2. R (SUC n) m1 /\ R (SUC n) m2 ==> m1 = m2

    # Get R c h n (@m. R c h n m) under existence at n.
    ex_term_n = exist_n._concl
    th_R_n_atP = ELIM_EX(pred_R_n, ex_term_n, lambda th: th)                   # {ex_term_n} |- R c h n (@m. R c h n m)
    th_R_n_atP_clean = PROVE_HYP(exist_n, th_R_n_atP)                          # |- R c h n (@m. R n m)

    # R_STEP gives R c h (SUC n) (h n (@m. R n m)).
    sel_pred_R_n = mk_comb(sel_const, pred_R_n)                                # @m. R c h n m  (= fn n after beta)
    h_n_selRn = mk_comb(mk_comb(_h, _n), sel_pred_R_n)
    R_step_at = SPEC(sel_pred_R_n, SPEC(_n, R_STEP))                            # |- R n (@m...) ==> R (SUC n) (h n (@m...))
    R_sn_h_n_sel = MP(R_step_at, th_R_n_atP_clean)                              # |- R (SUC n) (h n (@m. R n m))

    # Also R c h (SUC n) (@m. R c h (SUC n) m) using SELECT_AX.
    pred_R_sn_term = mk_abs(_m, _mk_R(_c, _h, mk_suc(_n), _m))
    exist_sn = CONJUNCT1(R_unique_sn)
    ex_term_sn = exist_sn._concl
    th_R_sn_atP = ELIM_EX(pred_R_sn_term, ex_term_sn, lambda th: th)
    th_R_sn_atP_clean = PROVE_HYP(exist_sn, th_R_sn_atP)                        # |- R (SUC n) (@m. R (SUC n) m)
    sel_pred_R_sn = mk_comb(sel_const, pred_R_sn_term)                           # @m. R c h (SUC n) m  (= fn (SUC n) after beta)

    # Apply uniqueness at SUC n: (@m. R (SUC n) m) = h n (@m. R n m).
    unique_at_sn = SPEC(h_n_selRn, SPEC(sel_pred_R_sn, unique_sn))               # |- R (SUC n) (@m..) /\ R (SUC n) (h n (@m..)) ==> (@m..) = h n (@m..)
    sel_sn_eq_hn = MP(unique_at_sn, CONJ(th_R_sn_atP_clean, R_sn_h_n_sel))
    # sel_sn_eq_hn : |- (@m. R (SUC n) m) = h n (@m. R n m).

    # fn (SUC n) BETA-reduces to (@m. R (SUC n) m).
    fn_sn = fn_app(mk_suc(_n))
    beta_fn_sn = BETA_CONV(fn_sn)                                                # |- fn (SUC n) = @m. R (SUC n) m
    # h n (fn n) = h n (@m. R n m)  via AP_TERM(h n, BETA_CONV(fn n)).
    fn_n = fn_app(_n)
    beta_fn_n = BETA_CONV(fn_n)                                                   # |- fn n = @m. R n m
    h_n_fnn_eq = AP_TERM(mk_comb(_h, _n), beta_fn_n)                              # |- h n (fn n) = h n (@m. R n m)
    # Combine: fn (SUC n) = @m. R (SUC n) m = h n (@m. R n m) = h n (fn n).
    fn_sn_eq_h_n_fnn = TRANS(beta_fn_sn, TRANS(sel_sn_eq_hn, SYM(h_n_fnn_eq)))    # |- fn (SUC n) = h n (fn n)
    forall_n_step = GEN(_n, fn_sn_eq_h_n_fnn)                                      # |- !n. fn (SUC n) = h n (fn n)

    # Combine and existential-introduce fn.
    combined = CONJ(fn_1_eq_c, forall_n_step)                                       # |- fn 1 = c /\ !n. fn (SUC n) = h n (fn n)
    # Build  ?fn. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
    # Predicate \fn. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
    fn_var = _fn
    fn_1_var = mk_comb(fn_var, ONE)
    fn_sn_var = mk_comb(fn_var, mk_suc(_n))
    fn_n_var = mk_comb(fn_var, _n)
    body_pred = mk_and(mk_eq(fn_1_var, _c),
                        mk_forall(_n,
                            mk_eq(fn_sn_var,
                                  mk_comb(mk_comb(_h, _n), fn_n_var))))
    pred_fn = mk_abs(fn_var, body_pred)
    exist_fn = EXISTS(pred_fn, fn_body, combined)                                    # |- ?fn. fn 1 = c /\ !n. fn (SUC n) = h n (fn n)

    return GEN(_c, GEN(_h, exist_fn))


NUM_RECURSION = _prove_num_recursion()


def _selftest_R():
    from logic import pp_thm
    print("R_AT_1:        ", pp_thm(R_AT_1))
    print("R_STEP:        ", pp_thm(R_STEP))
    print("R_UNIQUE_BASE: ", pp_thm(R_UNIQUE_BASE))
    print("R_UNIQUE_STEP: ", pp_thm(R_UNIQUE_STEP))
    print("R_UNIQUE:      ", pp_thm(R_UNIQUE))
    print("NUM_RECURSION: ", pp_thm(NUM_RECURSION))


if __name__ == "__main__":
    _selftest_R()
