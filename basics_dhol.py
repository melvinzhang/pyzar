"""Derived layer for fusion_dhol.

Reproduces the constants and rules that fusion_dhol used to ship as
kernel primitives, now built on top of the 10-rule HOL Light core plus
the DHOL-specific typing layer:

  T, TRUTH               via T_DEF.
  /\\, CONJ              via AND_DEF, with CONJUNCT1 / CONJUNCT2.
  ==>, mk_imp            via IMP_DEF (\\p q. (p /\\ q) = p), with
                         is_imp / dest_imp helpers.
  IMP_TYPE               typing-layer derived rule for ==>.
  DISCH, MP              derived per HOL Light bool.ml.
  ETA_AX, ETA            ETA_AX is an axiom polymorphic in a rank-1
                         type operator `B : (x:A)→tp`; ETA wraps it by
                         building the TypeAbs for B from the Pi codomain
                         the user supplies.

Several derived rules take an *extra typing certificate* alongside the
`thm` they consume. In HOL Light the analogous derivation uses
`REFL : term -> thm`, but DHOL's REFL takes a `typing_thm`, so callers
must supply the typing witness for the term whose reflexivity is being
exploited. The wrappers `DISCH(F_th, th)` and `MP(imp_th, ant_th)`
expose the same signature the kernel used to and rebuild the witnesses
they need internally."""

from __future__ import annotations

from fusion_dhol import (
    Var, Const, Comb, Abs, Pi, Tyvar, Tyapp,
    TyopVar, TyopApp, TypeAbs, TyEqAssume,
    typing_thm, thm, type_eq_thm,
    bool_ty, aty, safe_mk_eq, mk_arrow,
    VAR, CONST, LAMBDA, CONV,
    APP as _kernel_APP,
    MK_COMB as _kernel_MK_COMB,
    REFL, ASSUME, BETA,
    ABS as _kernel_ABS,
    TM_CONG_BASE as _kernel_TM_CONG_BASE,
    EQ_MP, DEDUCT_ANTISYM_RULE, INST, INST_TYPE,
    EQ_TY_CONV,
    SUBSUME, ST_FORGET,
    TYPE_OF, LHS_TYPING, RHS_TYPING, CONCL_TYPING,
    Assume, get_const_phi, get_const_type, type_eq, type_subst,
    subst_in_type, Subtype,
    new_basic_definition, new_axiom, new_type_eq_axiom, interpret,
    HolError, frees, vfree_in,
    _is_eq, _lhs, _rhs, _eq_tag,
    _pp_tm, _pp_ty,
)


# ---------------------------------------------------------------------------
# Bridge-wrapping APP and MK_COMB.
#
# The kernel ships strictly-homogeneous APP / MK_COMB (definitional
# domain match required). We expose the same names as wrappers that
# accept an optional propositional domain bridge and pre-CONV /
# pre-EQ_TY_CONV the argument before delegating. basics_dhol's own
# internal calls pass eq=None and so go straight through.
# ---------------------------------------------------------------------------


def APP(f_th: typing_thm, a_th: typing_thm,
        eq: type_eq_thm | None = None) -> typing_thm:
    """`Γ |- f : Pi(x:A). B`, `Γ |- a : A'` and optional `Γ |- A == A'`
       →  `Γ |- f a : B[a/x]`. Without `eq`, equivalent to kernel APP."""
    if eq is not None:
        a_th = CONV(a_th, eq)
    return _kernel_APP(f_th, a_th)


def MK_COMB(th1: thm, th2: thm,
            eq: type_eq_thm | None = None,
            cod_eq: type_eq_thm | None = None) -> thm:
    """`Γ |- f =_Pi(x:A).B f'`, `Γ |- a =_A' a'` and optional `eq : A == A'`
       →  `Γ |- f a =_B[a/x] f' a'`. With `cod_eq` (the dependent-codomain
       bridge), discharges the heterogeneous result-type case via
       `MK_COMB_HETERO_AX`. Without `eq` / `cod_eq`, equivalent to kernel
       MK_COMB."""
    if eq is not None:
        th2 = EQ_TY_CONV(th2, eq)
    if cod_eq is None:
        return _kernel_MK_COMB(th1, th2)
    return _mk_comb_hetero(th1, th2, cod_eq)


# ---------------------------------------------------------------------------
# SYM: needs the LHS's typing certificate because DHOL REFL is typing-driven.
# ---------------------------------------------------------------------------


def SYM(th: thm) -> thm:
    """asl |- a = b   →   asl |- b = a.

    HOL Light's SYM uses REFL on the equation's LHS term; the DHOL
    kernel's REFL requires a typing_thm, which we recover from the
    equation tag via LHS_TYPING. No threading tax."""
    lhs_th = LHS_TYPING(th)
    A = lhs_th._ty
    eq_const_th = CONST("=", (A,))
    refl_eq = REFL(eq_const_th)                 # |- (=) = (=)
    partial = MK_COMB(refl_eq, th)              # |- (=) a = (=) b
    refl_a = REFL(lhs_th)                       # |- a = a
    eq_eq = MK_COMB(partial, refl_a)            # |- (a = a) = (b = a)
    return EQ_MP(eq_eq, refl_a)                 # |- b = a


def TRANS(th1: thm, th2: thm) -> thm:
    """th1: asl1 |- a = b at A,  th2: asl2 |- b = c at A
                         → asl1 ∪ asl2 |- a = c at A.

    Derived (HOL Light keeps it primitive for performance, not
    minimality). Equation types must agree definitionally; align with
    EQ_TY_CONV first if they differ. Middle terms must α-match.

    Construction: AP_TERM (= a) th2 gives |- (a = b) = (a = c); EQ_MP
    with th1 lands a = c."""
    a_th = LHS_TYPING(th1)
    A = a_th._ty
    eq_const_th = CONST("=", (A,))
    eq_a_th = APP(eq_const_th, a_th)             # |- (= a) : A → bool
    refl_eq_a = REFL(eq_a_th)                    # |- (= a) = (= a)
    # MK_COMB enforces both the type-tag and middle-term checks.
    eq_eq = MK_COMB(refl_eq_a, th2)              # |- (a = b) = (a = c)
    return EQ_MP(eq_eq, th1)                     # |- a = c


def UNRESTRICT(t_th: typing_thm) -> typing_thm:
    """Elim (forget the refinement):  Gamma |- t : A|p
                                      -----------------
                                      Gamma |- t : A

    Derived as `SUBSUME(t_th, ST_FORGET(A|p))`. The kernel doesn't
    need to ship this rule -- forget-and-subsume is the standard
    factoring."""
    return SUBSUME(t_th, ST_FORGET(t_th._ty))


# ---------------------------------------------------------------------------
# T (truth)
# ---------------------------------------------------------------------------

_p_bool = Var("p", bool_ty)
_lam_p_p_th = LAMBDA(_p_bool, VAR(_p_bool))     # |- (\p:bool. p) : bool -> bool
_lam_p_p_ty = _lam_p_p_th._ty
_T_RHS_th = APP(
    APP(CONST("=", (_lam_p_p_ty,)), _lam_p_p_th),
    _lam_p_p_th,
)
# T_DEF: |- T = ((\p:bool. p) = (\p:bool. p))
T_DEF = new_basic_definition(Var("T", bool_ty), _T_RHS_th)

_T_const_th = CONST("T")                         # |- T : bool
T_tm: term = _T_const_th._tm

# TRUTH: |- T
_T_DEF_SYM = SYM(T_DEF)                          # |- ((\p.p) = (\p.p)) = T
TRUTH = EQ_MP(_T_DEF_SYM, REFL(_lam_p_p_th))


# ---------------------------------------------------------------------------
# /\ (conjunction)
# ---------------------------------------------------------------------------

_bbb = mk_arrow(bool_ty, mk_arrow(bool_ty, bool_ty))     # bool -> bool -> bool
_p_var = Var("p", bool_ty)
_q_var = Var("q", bool_ty)
_f_var = Var("f", _bbb)

# (\f:bbb. f p q) typing
_fpq_th = LAMBDA(_f_var, APP(APP(VAR(_f_var), VAR(_p_var)), VAR(_q_var)))
# (\f:bbb. f T T) typing
_fTT_th = LAMBDA(_f_var, APP(APP(VAR(_f_var), _T_const_th), _T_const_th))
# (\f. f p q) = (\f. f T T)
_eq_at_fty = CONST("=", (_fpq_th._ty,))
_and_body_inner_th = APP(APP(_eq_at_fty, _fpq_th), _fTT_th)
# \q. (...)
_and_body_q_th = LAMBDA(_q_var, _and_body_inner_th)
# \p q. (...)
_and_body_th = LAMBDA(_p_var, _and_body_q_th)

# AND_DEF: |- /\ = (\p q. (\f. f p q) = (\f. f T T))
AND_DEF = new_basic_definition(Var("/\\", _bbb), _and_body_th)


# ---------------------------------------------------------------------------
# EQT_INTRO / EQT_ELIM: bridges between |- p and |- p = T.
# ---------------------------------------------------------------------------


def EQT_INTRO(th: thm) -> thm:
    """asl |- p   →   asl |- p = T."""
    # Build polymorphic lemma |- p = (p = T) for free p, then INST at the
    # user's term via CONCL_TYPING.
    p_free = Var("p", bool_ty)
    p_free_th = VAR(p_free)
    p_eq_T_typing = APP(
        APP(CONST("=", (bool_ty,)), p_free_th),
        _T_const_th,
    )                                            # typing |- (p = T) : bool

    asm_p = ASSUME(p_free_th)                    # [p] |- p
    th1 = DEDUCT_ANTISYM_RULE(asm_p, TRUTH)      # [p] |- p = T

    asm_eq = ASSUME(p_eq_T_typing)               # [p = T] |- p = T
    sym_asm_eq = SYM(asm_eq)                     # [p = T] |- T = p
    th2 = EQ_MP(sym_asm_eq, TRUTH)               # [p = T] |- p

    pth = DEDUCT_ANTISYM_RULE(th2, th1)          # |- p = (p = T)
    pth_at_p = INST([(CONCL_TYPING(th), p_free)], pth)
    return EQ_MP(pth_at_p, th)                   # asl |- th._concl = T


def EQT_ELIM(th: thm) -> thm:
    """asl |- p = T   →   asl |- p."""
    return EQ_MP(SYM(th), TRUTH)


# ---------------------------------------------------------------------------
# Polymorphic CONJ lemma:  [p, q] |- p /\ q   for free bool vars p, q.
# ---------------------------------------------------------------------------

def _and_typing(p_th: typing_thm, q_th: typing_thm) -> typing_thm:
    """Build typing |- (p /\\ q) : bool from p:bool, q:bool."""
    return APP(APP(CONST("/\\"), p_th), q_th)


def _build_conj_pth() -> thm:
    p_th = VAR(_p_var)
    q_th = VAR(_q_var)
    asm_p = ASSUME(p_th)                              # [p] |- p
    asm_q = ASSUME(q_th)                              # [q] |- q
    p_eq_T = EQT_INTRO(asm_p)                         # [p] |- p = T
    q_eq_T = EQT_INTRO(asm_q)                         # [q] |- q = T

    refl_f = REFL(VAR(_f_var))                        # |- f = f
    fp_eq_fT = MK_COMB(refl_f, p_eq_T)                # [p] |- f p = f T
    fpq_eq_fTT = MK_COMB(fp_eq_fT, q_eq_T)            # [p, q] |- f p q = f T T
    lam_eq = _kernel_ABS(_f_var, fpq_eq_fTT)          # [p, q] |- (\f. f p q) = (\f. f T T)

    # |- /\ p q = ((\f. f p q) = (\f. f T T))   (via AND_DEF + 2× BETA)
    refl_p = REFL(p_th)
    refl_q = REFL(q_th)
    and_p_eq = MK_COMB(AND_DEF, refl_p)
    beta_outer = BETA(APP(_and_body_th, VAR(_p_var)))
    lam_after_p = TRANS(and_p_eq, beta_outer)
    and_pq_eq = MK_COMB(lam_after_p, refl_q)
    beta_inner = BETA(APP(_and_body_q_th, VAR(_q_var)))
    and_pq_eq_unfolded = TRANS(and_pq_eq, beta_inner)

    sym_and = SYM(and_pq_eq_unfolded)                 # |- ((\f. f p q) = (\f. f T T)) = /\ p q
    return EQ_MP(sym_and, lam_eq)                     # [p, q] |- /\ p q


_CONJ_PTH = _build_conj_pth()


def mk_and(p: term, q: term) -> term:
    """Build the term `p /\\ q` at type bool."""
    and_ty = mk_arrow(bool_ty, mk_arrow(bool_ty, bool_ty))
    return Comb(Comb(Const("/\\", and_ty), p), q)


def CONJ(th1: thm, th2: thm) -> thm:
    """th1: asl1 |- p, th2: asl2 |- q   →   asl1 ∪ asl2 |- p /\\ q."""
    inst_th = INST(
        [(CONCL_TYPING(th1), _p_var), (CONCL_TYPING(th2), _q_var)],
        _CONJ_PTH,
    )
    return PROVE_HYP(th2, PROVE_HYP(th1, inst_th))


def PROVE_HYP(ath: thm, bth: thm) -> thm:
    """`ath : asl1 |- a`, `bth : asl2 |- b`. If `a` is one of bth's
    asl entries, returns `asl1 ∪ (asl2 - a) |- b`; else `bth` unchanged.

    Derived as `EQ_MP(DEDUCT_ANTISYM_RULE(ath, bth), ath)` -- standard
    HOL Light boilerplate."""
    # DEDUCT_ANTISYM_RULE(ath: asl1 |- A, bth: asl2 |- B):
    #   result asl = (asl1 - B) ∪ (asl2 - A);  concl = A = B.
    # EQ_MP with ath gives asl1 ∪ (asl2 - A) |- B.
    eq = DEDUCT_ANTISYM_RULE(ath, bth)
    return EQ_MP(eq, ath)


# ---------------------------------------------------------------------------
# Polymorphic CONJUNCT1 / CONJUNCT2 lemmas.
#
# CONJUNCT1: [p /\ q] |- p,   CONJUNCT2: [p /\ q] |- q
# ---------------------------------------------------------------------------


def _build_conjunct1_pth() -> thm:
    p_th = VAR(_p_var)
    q_th = VAR(_q_var)
    pq_and_th = _and_typing(p_th, q_th)
    asm_pq = ASSUME(pq_and_th)                        # [p /\ q] |- p /\ q

    # Unfold via AND_DEF + 2 BETAs:
    # /\ p q  =  (\f. f p q) = (\f. f T T)
    refl_p = REFL(p_th)
    refl_q = REFL(q_th)
    and_p_eq = MK_COMB(AND_DEF, refl_p)
    beta_outer = BETA(APP(_and_body_th, VAR(_p_var)))
    lam_after_p = TRANS(and_p_eq, beta_outer)
    and_pq_eq = MK_COMB(lam_after_p, refl_q)
    beta_inner = BETA(APP(_and_body_q_th, VAR(_q_var)))
    and_pq_unfolded = TRANS(and_pq_eq, beta_inner)
    # and_pq_unfolded : |- /\ p q = ((\f. f p q) = (\f. f T T))

    # Apply EQ_MP to asm_pq to get [p /\ q] |- (\f. f p q) = (\f. f T T)
    asm_eq = EQ_MP(and_pq_unfolded, asm_pq)

    # Pick selector f = \x:bool y:bool. x to extract p.
    # (\x y. x) p q = p, by 2 BETAs (with bound names matching).
    # Use the same _p_var, _q_var names so beta is trivial.
    sel1_lam_inner = LAMBDA(_q_var, VAR(_p_var))       # \q. p   : bool -> bool
    sel1_th = LAMBDA(_p_var, sel1_lam_inner)           # \p q. p : bool -> bool -> bool

    # MK_COMB sel1_th into asm_eq:
    # asm_eq: [pq] |- (\f. f p q) = (\f. f T T)
    # Use MK_COMB(asm_eq, REFL(sel1)) — no, asm_eq's both sides take f.
    # We need to apply both sides to sel1 separately:
    # |- (\f. f p q) sel1 = (\f. f T T) sel1
    # MK_COMB(asm_eq, REFL(sel1_th)) gives that.
    refl_sel = REFL(sel1_th)
    app_eq = MK_COMB(asm_eq, refl_sel)
    # app_eq: [pq] |- (\f. f p q) sel1 = (\f. f T T) sel1

    # BETA-reduce both sides. The LHS redex (\f. f p q) sel1 is NOT a trivial
    # redex (arg sel1 != f). We need a workaround: build (\f. f p q) f as a
    # trivial redex, BETA it, then INST [sel1/f].
    redex_lhs_trivial = APP(_fpq_th, VAR(_f_var))      # (\f. f p q) f
    beta_lhs = BETA(redex_lhs_trivial)                  # |- (\f. f p q) f = f p q
    # INST [sel1_th / f] to get |- (\f. f p q) sel1 = sel1 p q
    beta_lhs_at_sel = INST([(sel1_th, _f_var)], beta_lhs)

    # Same for RHS:
    redex_rhs_trivial = APP(_fTT_th, VAR(_f_var))       # (\f. f T T) f
    beta_rhs = BETA(redex_rhs_trivial)                   # |- (\f. f T T) f = f T T
    beta_rhs_at_sel = INST([(sel1_th, _f_var)], beta_rhs)

    # Chain to extract sel1 p q = sel1 T T from app_eq.
    # app_eq : (\f. f p q) sel1 = (\f. f T T) sel1
    # SYM(beta_lhs_at_sel) : sel1 p q = (\f. f p q) sel1
    # SYM(beta_rhs_at_sel) flipped via TRANS:
    sym_lhs = SYM(beta_lhs_at_sel)
    step1 = TRANS(sym_lhs, app_eq)
    # step1: [pq] |- sel1 p q = (\f. f T T) sel1
    step2 = TRANS(step1, beta_rhs_at_sel)
    # step2: [pq] |- sel1 p q = sel1 T T

    # Now sel1 p q reduces to p (by 2 BETAs); sel1 T T reduces to T.
    # sel1 = \p q. p, so (\p q. p) p q = p by trivial redexes.
    beta_sel_p_outer = BETA(APP(sel1_th, VAR(_p_var)))  # |- (\p q. p) p = \q. p
    refl_q_var = REFL(VAR(_q_var))
    sel_p_after1 = MK_COMB(beta_sel_p_outer, refl_q_var)
    # (\q. p) q = p — trivial redex.
    lam_q_p_th = LAMBDA(_q_var, VAR(_p_var))
    beta_inner_sel = BETA(APP(lam_q_p_th, VAR(_q_var)))
    sel_p_fully = TRANS(sel_p_after1, beta_inner_sel)
    # sel_p_fully : |- (\p q. p) p q = p

    # sel1 T T = T via INST [T/p_var, T/q_var] on sel_p_fully.
    # The bound vars inside sel1's abstraction are alpha-renamed away from
    # the outer free p_var, q_var by the substitution discipline.
    sel_T_fully = INST([(_T_const_th, _p_var), (_T_const_th, _q_var)], sel_p_fully)
    # sel_T_fully : |- (\p q. p) T T = T

    # Combine: step2 says sel1 p q = sel1 T T.
    # sel1 p q = p (sel_p_fully) and sel1 T T = T (sel_T_fully).
    sym_sel_p = SYM(sel_p_fully)                       # |- p = (\p q. p) p q
    step3 = TRANS(sym_sel_p, step2)                    # [pq] |- p = (\p q. p) T T
    step4 = TRANS(step3, sel_T_fully)                  # [pq] |- p = T
    return EQT_ELIM(step4)


def _build_conjunct2_pth() -> thm:
    # Mirror of CONJUNCT1 with selector \p q. q.
    p_th = VAR(_p_var)
    q_th = VAR(_q_var)
    pq_and_th = _and_typing(p_th, q_th)
    asm_pq = ASSUME(pq_and_th)

    refl_p = REFL(p_th)
    refl_q = REFL(q_th)
    and_p_eq = MK_COMB(AND_DEF, refl_p)
    beta_outer = BETA(APP(_and_body_th, VAR(_p_var)))
    lam_after_p = TRANS(and_p_eq, beta_outer)
    and_pq_eq = MK_COMB(lam_after_p, refl_q)
    beta_inner = BETA(APP(_and_body_q_th, VAR(_q_var)))
    and_pq_unfolded = TRANS(and_pq_eq, beta_inner)
    asm_eq = EQ_MP(and_pq_unfolded, asm_pq)

    sel2_lam_inner = LAMBDA(_q_var, VAR(_q_var))       # \q. q
    sel2_th = LAMBDA(_p_var, sel2_lam_inner)           # \p q. q

    refl_sel = REFL(sel2_th)
    app_eq = MK_COMB(asm_eq, refl_sel)

    beta_lhs = BETA(APP(_fpq_th, VAR(_f_var)))
    beta_lhs_at_sel = INST([(sel2_th, _f_var)], beta_lhs)
    beta_rhs = BETA(APP(_fTT_th, VAR(_f_var)))
    beta_rhs_at_sel = INST([(sel2_th, _f_var)], beta_rhs)

    sym_lhs = SYM(beta_lhs_at_sel)
    step1 = TRANS(sym_lhs, app_eq)
    step2 = TRANS(step1, beta_rhs_at_sel)

    sel_p_outer = APP(sel2_th, VAR(_p_var))
    beta_sel_p_outer = BETA(sel_p_outer)               # (\p q. q) p = \q. q
    refl_q_var = REFL(VAR(_q_var))
    sel_p_after1 = MK_COMB(beta_sel_p_outer, refl_q_var)
    lam_q_q_th = LAMBDA(_q_var, VAR(_q_var))
    beta_inner_sel = BETA(APP(lam_q_q_th, VAR(_q_var)))
    sel_p_fully = TRANS(sel_p_after1, beta_inner_sel)
    # sel_p_fully : |- (\p q. q) p q = q

    sel_T_fully = INST([(_T_const_th, _p_var), (_T_const_th, _q_var)], sel_p_fully)
    # sel_T_fully : |- (\p q. q) T T = T

    sym_sel_p = SYM(sel_p_fully)
    step3 = TRANS(sym_sel_p, step2)
    step4 = TRANS(step3, sel_T_fully)                  # [pq] |- q = T
    return EQT_ELIM(step4)


_CONJUNCT1_PTH = _build_conjunct1_pth()
_CONJUNCT2_PTH = _build_conjunct2_pth()


def _conj_typings(th: thm) -> tuple:
    """`th : asl |- p /\\ q`  →  (typing for p, typing for q), both at bool.

    Uses TYPE_OF with empty asl. If the conjuncts contain propositional
    CONV bridges in their intrinsic structure, TYPE_OF will fail --
    normalize via EQ_TY_CONV at the boundary before applying CONJUNCT*.
    """
    concl = th._concl
    if not (isinstance(concl, Comb) and isinstance(concl.fun, Comb)
            and isinstance(concl.fun.fun, Const)
            and concl.fun.fun.name == "/\\"):
        raise HolError("CONJUNCT*: conclusion is not a /\\")
    return (TYPE_OF([], concl.fun.arg), TYPE_OF([], concl.arg))


def CONJUNCT1(th: thm) -> thm:
    """`th : asl |- p /\\ q`  →  `asl |- p`."""
    p_th, q_th = _conj_typings(th)
    return PROVE_HYP(th, INST([(p_th, _p_var), (q_th, _q_var)], _CONJUNCT1_PTH))


def CONJUNCT2(th: thm) -> thm:
    """`th : asl |- p /\\ q`  →  `asl |- q`."""
    p_th, q_th = _conj_typings(th)
    return PROVE_HYP(th, INST([(p_th, _p_var), (q_th, _q_var)], _CONJUNCT2_PTH))


# ---------------------------------------------------------------------------
# ==> (implication)
# ---------------------------------------------------------------------------

# IMP_DEF: |- ==> = \p q. (p /\ q) = p
_p_and_q_th = _and_typing(VAR(_p_var), VAR(_q_var))
_imp_body_inner_th = APP(
    APP(CONST("=", (bool_ty,)), _p_and_q_th),
    VAR(_p_var),
)
_imp_body_th = LAMBDA(_p_var, LAMBDA(_q_var, _imp_body_inner_th))
IMP_DEF = new_basic_definition(Var("==>", _bbb), _imp_body_th)


def mk_imp(F: term, G: term) -> term:
    """Build `F ==> G` at type bool."""
    return Comb(Comb(Const("==>", _bbb), F), G)


def is_imp(c: term) -> bool:
    return (
        isinstance(c, Comb)
        and isinstance(c.fun, Comb)
        and isinstance(c.fun.fun, Const)
        and c.fun.fun.name == "==>"
    )


def dest_imp(c: term) -> tuple:
    """Return (antecedent, consequent) from `F ==> G`."""
    if not is_imp(c):
        raise HolError("dest_imp: not an implication")
    return (c.fun.arg, c.arg)


def _build_imp_unfold_pth() -> thm:
    """Polymorphic |- (==> p q) = ((p /\\ q) = p) over free p, q : bool."""
    p_canon = VAR(_p_var)
    q_canon = VAR(_q_var)
    refl_p = REFL(p_canon)
    refl_q = REFL(q_canon)
    imp_p_eq = MK_COMB(IMP_DEF, refl_p)
    beta_outer = BETA(APP(_imp_body_th, VAR(_p_var)))
    lam_after_p = TRANS(imp_p_eq, beta_outer)
    imp_pq_eq = MK_COMB(lam_after_p, refl_q)
    inner_lam_q_th = LAMBDA(_q_var, _imp_body_inner_th)
    beta_inner = BETA(APP(inner_lam_q_th, VAR(_q_var)))
    return TRANS(imp_pq_eq, beta_inner)


_IMP_UNFOLD_PTH = _build_imp_unfold_pth()


def _imp_unfold_eq(p_th: typing_thm, q_th: typing_thm) -> thm:
    """`|- (p ==> q) = ((p /\\ q) = p)` for user-supplied p, q : bool."""
    return INST([(p_th, _p_var), (q_th, _q_var)], _IMP_UNFOLD_PTH)


# ---------------------------------------------------------------------------
# IMP_TYPE, DISCH, MP
# ---------------------------------------------------------------------------


def _require_bool(t_th: typing_thm, ctx: str) -> None:
    from fusion_dhol import type_eq as _type_eq
    if not _type_eq(t_th._ty, bool_ty):
        raise HolError(f"{ctx}: non-bool type {_pp_ty(t_th._ty)}")


def IMP_TYPE(F_th: typing_thm, G_th: typing_thm) -> typing_thm:
    """`Gamma |- F : bool, Gamma, ▷F |- G : bool  →  Gamma |- F ==> G : bool`.

    Mirrors fusion_dhol's old kernel rule. F is removed from G_th's
    asl, matching the old `Rule D` behaviour."""
    from fusion_dhol import term_remove
    _require_bool(F_th, "IMP_TYPE antecedent")
    _require_bool(G_th, "IMP_TYPE consequent")
    G_cleaned = typing_thm(
        term_remove(F_th._tm, G_th._asl),
        G_th._tm,
        G_th._ty,
    )
    return APP(APP(CONST("==>"), F_th), G_cleaned)


def DISCH(F_th: typing_thm, th: thm) -> thm:
    """asl, F |- G  →  asl |- F ==> G  (HOL Light bool.ml derivation).

    F_th : Gamma |- F : bool certifies the antecedent; the consequent's
    typing is recovered via CONCL_TYPING on th."""
    _require_bool(F_th, "DISCH antecedent")
    G_typing = CONCL_TYPING(th)
    F_and_G_typing = _and_typing(F_th, G_typing)

    th1 = CONJ(ASSUME(F_th), th)                       # asl, F |- F /\ G
    th2 = CONJUNCT1(ASSUME(F_and_G_typing))            # [F /\ G] |- F
    th3 = DEDUCT_ANTISYM_RULE(th1, th2)                # asl |- (F /\ G) = F
    sym_imp = SYM(_imp_unfold_eq(F_th, G_typing))      # |- ((F /\ G) = F) = (F ==> G)
    return EQ_MP(sym_imp, th3)


def MP(imp_th: thm, ant_th: thm) -> thm:
    """`asl1 |- F ==> G`, `asl2 |- F`  →  `asl1 ∪ asl2 |- G`.

    Derived via IMP_DEF + CONJ + CONJUNCT2."""
    if not is_imp(imp_th._concl):
        raise HolError("MP: first argument is not an implication")
    F_tm, G_tm = dest_imp(imp_th._concl)
    if not _alpha_eq(F_tm, ant_th._concl):
        raise HolError("MP: antecedent does not match")

    # Both typings via the kernel's structural rules. If G carries a
    # propositional CONV bridge inside its intrinsic shape, the caller
    # must EQ_TY_CONV-normalize the implication before MP.
    F_typing = CONCL_TYPING(ant_th)
    G_typing = TYPE_OF([], G_tm)
    imp_unfold = _imp_unfold_eq(F_typing, G_typing)    # |- (F ==> G) = ((F /\ G) = F)
    fg_eq_F = EQ_MP(imp_unfold, imp_th)                # asl1 |- (F /\ G) = F
    sym_fg = SYM(fg_eq_F)                              # asl1 |- F = (F /\ G)
    f_and_g_thm = EQ_MP(sym_fg, ant_th)                # asl1 ∪ asl2 |- F /\ G
    return CONJUNCT2(f_and_g_thm)


def _alpha_eq(a, b) -> bool:
    from fusion_dhol import _tm_alpha
    return _tm_alpha([], a, b)


# ---------------------------------------------------------------------------
# ETA: axiomatised at a fully-dependent Pi via a rank-1 type operator B.
#
# ETA_AX : (A:tp, B:(x:A)→tp, f:Pi(x:A). B(x)) ▷ (\x:A. f x) = f
#
# The non-dependent case (B does not mention x) is recovered by passing
# a constant TypeAbs: σ[B] = TypeAbs((x:A,), B_ty) where B_ty doesn't
# mention x.
# ---------------------------------------------------------------------------


_A_tv = Tyvar("A")
_x_A_var = Var("x", _A_tv)
_B_op = TyopVar("B", (_x_A_var,))
# Pi(x:A). B(x)
_B_at_x = TyopApp("B", (_x_A_var,))
_f_dep_ty = Pi(_x_A_var, _B_at_x)
_f_dep_var = Var("f", _f_dep_ty)
# (\x:A. f x) : Pi(x:A). B(x)
_lam_fx_th = LAMBDA(_x_A_var, APP(VAR(_f_dep_var), VAR(_x_A_var)))
_eta_form = safe_mk_eq(
    _f_dep_ty,
    _lam_fx_th._tm,
    VAR(_f_dep_var)._tm,
)
ETA_AX = new_axiom(
    typing_thm([], _eta_form, bool_ty),
    phi=(_A_tv, _B_op, _f_dep_var),
)


def ETA(t_th: typing_thm) -> thm:
    """`Gamma |- t : Pi(x:A). B(x)   →   Gamma |- t = (\\x:A. t x)`.

    Handles the fully-dependent case: the Pi codomain may mention the
    binder. The B operator's σ-evidence is built by wrapping the
    codomain in a `TypeAbs` over the Pi binder; the non-dependent case
    falls out as a TypeAbs whose body doesn't mention the bvar."""
    ty = t_th._ty
    if not isinstance(ty, Pi):
        raise HolError(f"ETA: term type is not a Pi (got {_pp_ty(ty)})")
    A_ty = ty.bvar.ty
    B_typeabs = TypeAbs((ty.bvar,), ty.body)
    eta_at = interpret(ETA_AX, (A_ty, B_typeabs, t_th))
    return SYM(eta_at)


# ---------------------------------------------------------------------------
# Heterogeneous-type axioms.
#
# The kernel ships only homogeneous MK_COMB / ABS / TM_CONG_BASE and no
# TY_CONG_PI; the four heterogeneous bridges are derived here as axioms
# over `TyEqAssume` (type-equality assumptions in Φ):
#
#   PI_CONG_AX           -- replaces kernel TY_CONG_PI
#   MK_COMB_HETERO_AX    -- replaces kernel MK_COMB's cod_eq
#   TM_CONG_HETERO_AX    -- replaces kernel TM_CONG_BASE's cod_eq
#   ABS_HETERO_AX        -- replaces kernel ABS's ty_eq
#
# The basics_dhol wrappers below expose the previous kernel signatures
# (cod_eq / ty_eq keyword args; explicit TY_CONG_PI) by dispatching to
# these axioms.
# ---------------------------------------------------------------------------


# --- PI_CONG_AX -----------------------------------------------------------
# (A:tp, A':tp, B:(x:A)→tp, B':(x:A)→tp, ▷ A==A', ⟨x:A⟩ ▷ B(x)==B'(x))
#    ▷ Pi(x:A). B(x) == Pi(x:A'). B'(x)
#
# The user supplies `cod_eq` with a binder Var whose name they choose;
# the TyEqAssume σ uses the (user_vars, type_eq_thm) shape to align
# that name with the schematic.

_pi_A   = Tyvar("A_pi")
_pi_Ap  = Tyvar("A'_pi")
_pi_x_A = Var("x", _pi_A)
_pi_B   = TyopVar("B_pi", (_pi_x_A,))
_pi_Bp  = TyopVar("B'_pi", (_pi_x_A,))
_pi_lhs = Pi(_pi_x_A, TyopApp("B_pi", (_pi_x_A,)))
_pi_rhs = Pi(Var("x", _pi_Ap), TyopApp("B'_pi", (Var("x", _pi_Ap),)))

PI_CONG_AX = new_type_eq_axiom(
    type_eq_thm([], _pi_lhs, _pi_rhs),
    phi=(
        _pi_A, _pi_Ap, _pi_B, _pi_Bp,
        TyEqAssume((), _pi_A, _pi_Ap),
        TyEqAssume(
            (_pi_x_A,),
            TyopApp("B_pi", (_pi_x_A,)),
            TyopApp("B'_pi", (_pi_x_A,)),
        ),
    ),
)


def TY_CONG_PI(v: Var, dom_eq: type_eq_thm,
               cod_eq: type_eq_thm) -> type_eq_thm:
    """congPi:  Γ |- A == A'   Γ, x:A |- B == B'
               --------------------------------------------
               Γ |- Pi(x:A). B == Pi(x:A'). B'

    Derived via `PI_CONG_AX`. `v` is the binder name + type the user's
    `cod_eq` references; `v.ty` must be `dom_eq._lhs`. The user's
    binder name is mapped to the schematic via the TyEqAssume rename
    mechanism, so no name convention is imposed."""
    if not type_eq(v.ty, dom_eq._lhs):
        raise HolError("TY_CONG_PI: binder type does not match domain LHS")
    A_l, A_r = dom_eq._lhs, dom_eq._rhs
    B_typeabs = TypeAbs((v,), cod_eq._lhs)
    Bp_typeabs = TypeAbs((v,), cod_eq._rhs)
    return interpret(
        PI_CONG_AX,
        (A_l, A_r, B_typeabs, Bp_typeabs, dom_eq, ((v,), cod_eq)),
    )


# --- MK_COMB_HETERO_AX ----------------------------------------------------
# (A, B:(z:A)→tp,
#  f:Π(z:A).B(z), f':Π(z:A).B(z), a:A, a':A,
#  ▷ f = f', ▷ a = a', ▷ B(a) == B(a'))
#    ▷ f a = f' a'    at B(a)

_mkA = Tyvar("A_mk")
_mkz = Var("z_mk", _mkA)
_mkB = TyopVar("B_mk", (_mkz,))
_mk_pi_ty = Pi(_mkz, TyopApp("B_mk", (_mkz,)))
_mkf = Var("f_mk", _mk_pi_ty)
_mkfp = Var("f'_mk", _mk_pi_ty)
_mka = Var("a_mk", _mkA)
_mkap = Var("a'_mk", _mkA)
_mk_f_eq = safe_mk_eq(_mk_pi_ty, _mkf, _mkfp)
_mk_a_eq = safe_mk_eq(_mkA, _mka, _mkap)
_mk_body = safe_mk_eq(
    TyopApp("B_mk", (_mka,)),
    Comb(_mkf, _mka),
    Comb(_mkfp, _mkap),
)

MK_COMB_HETERO_AX = new_axiom(
    typing_thm([_mk_f_eq, _mk_a_eq], _mk_body, bool_ty),
    phi=(
        _mkA, _mkB, _mkf, _mkfp, _mka, _mkap,
        Assume(_mk_f_eq), Assume(_mk_a_eq),
        TyEqAssume((), TyopApp("B_mk", (_mka,)), TyopApp("B_mk", (_mkap,))),
    ),
)


def _mk_comb_hetero(th1: thm, th2: thm, cod_eq: type_eq_thm) -> thm:
    """Discharge MK_COMB's dependent-codomain bridge via
    MK_COMB_HETERO_AX. th1 : f =Pi(z:A).B(z) f',  th2 : a =A a',
    cod_eq : B(a) == B(a') (orientation-agnostic)."""
    f_ty = _eq_tag(th1._concl)
    if not isinstance(f_ty, Pi):
        raise HolError("MK_COMB: function-side equation type is not Pi")
    A_ty = _eq_tag(th2._concl)
    f_tm, fp_tm = _lhs(th1._concl), _rhs(th1._concl)
    a_tm, ap_tm = _lhs(th2._concl), _rhs(th2._concl)
    # Build TypeAbs B from the Pi codomain (captures the binder).
    B_typeabs = TypeAbs((f_ty.bvar,), f_ty.body)
    # Compute expected codomain types at a and a'.
    Ba = subst_in_type([(a_tm, f_ty.bvar)], f_ty.body)
    Bap = subst_in_type([(ap_tm, f_ty.bvar)], f_ty.body)
    if type_eq(cod_eq._lhs, Bap) and type_eq(cod_eq._rhs, Ba):
        cod_eq = TY_SYM(cod_eq)
    if not (type_eq(cod_eq._lhs, Ba) and type_eq(cod_eq._rhs, Bap)):
        raise HolError(
            f"MK_COMB: cod_eq does not bridge codomains "
            f"({_pp_ty(cod_eq._lhs)} == {_pp_ty(cod_eq._rhs)} vs "
            f"required {_pp_ty(Ba)} == {_pp_ty(Bap)})"
        )
    return interpret(
        MK_COMB_HETERO_AX,
        (
            A_ty, B_typeabs,
            typing_thm([], f_tm, f_ty),
            typing_thm([], fp_tm, f_ty),
            typing_thm([], a_tm, A_ty),
            typing_thm([], ap_tm, A_ty),
            th1, th2, cod_eq,
        ),
    )


# --- ABS_HETERO_AX --------------------------------------------------------
# (A, A', B:(z:A)→tp,
#  t:B(x), t':B(x),         -- x is the schematic free Var Var("x", A)
#  ▷ t = t' at B(x),
#  ▷ A == A')
#   ▷ (\x:A. t) = (\x:A'. t')    at Π(x:A). B(x)
#
# x is a *free* Var of type A in the body's type annotations; the Abs
# binders Var("x", A) / Var("x", A') capture it on each side.

_abs_A  = Tyvar("A_abs")
_abs_Ap = Tyvar("A'_abs")
_abs_x  = Var("x", _abs_A)         # schematic free Var, captured by Abs
_abs_x_Ap = Var("x", _abs_Ap)
_abs_B  = TyopVar("B_abs", (_abs_x,))
_abs_Bx = TyopApp("B_abs", (_abs_x,))
_abs_t  = Var("t_abs", _abs_Bx)
_abs_tp = Var("t'_abs", _abs_Bx)
_abs_body_eq = safe_mk_eq(_abs_Bx, _abs_t, _abs_tp)
_abs_pi_ty = Pi(_abs_x, _abs_Bx)
_abs_concl = safe_mk_eq(
    _abs_pi_ty,
    Abs(_abs_x, _abs_t),
    Abs(_abs_x_Ap, _abs_tp),
)

ABS_HETERO_AX = new_axiom(
    typing_thm([_abs_body_eq], _abs_concl, bool_ty),
    phi=(
        _abs_A, _abs_Ap, _abs_B,
        _abs_t, _abs_tp,
        Assume(_abs_body_eq),
        TyEqAssume((), _abs_A, _abs_Ap),
    ),
)


def ABS(v: Var, th: thm, ty_eq: type_eq_thm | None = None) -> thm:
    """congLambda':  Γ |- A == A'   Γ, x:A |- t =B t'
                    ------------------------------------------------
                    Γ |- (\\x:A. t) =Pi(x:A).B (\\x:A'. t')

    Without `ty_eq` the homogeneous case (kernel ABS). With `ty_eq`,
    the heterogeneous binder-type bridge is discharged via
    `ABS_HETERO_AX`. ``v`` must not occur free in any hypothesis,
    including the bridge's.

    The user's binder `v` is internally renamed to the schematic
    `Var("x", v.ty)` via `INST` on `th`; the resulting lambda has
    binder name `x` (alpha-equivalent to a hypothetical `v`-named
    result -- only the bound-name choice differs)."""
    if ty_eq is None:
        return _kernel_ABS(v, th)
    if any(vfree_in(v, a) for a in th._asl):
        raise HolError("ABS: bound variable occurs free in hypotheses")
    if any(vfree_in(v, a) for a in ty_eq._asl):
        raise HolError("ABS: bound variable occurs free in bridge hypotheses")
    A_user = v.ty
    A_p_user = _other_side_ty(ty_eq, A_user, "ABS")
    x_sch = Var("x", A_user)
    if v != x_sch:
        th = INST([(typing_thm([], x_sch, A_user), v)], th)
    body_ty = _eq_tag(th._concl)
    t_tm, tp_tm = _lhs(th._concl), _rhs(th._concl)
    B_typeabs = TypeAbs((x_sch,), body_ty)
    # Orient ty_eq so lhs == A_user, rhs == A_p_user (which is the
    # schematic order).
    if type_eq(ty_eq._lhs, A_p_user) and type_eq(ty_eq._rhs, A_user):
        ty_eq = TY_SYM(ty_eq)
    return interpret(
        ABS_HETERO_AX,
        (
            A_user, A_p_user, B_typeabs,
            typing_thm([], t_tm, body_ty),
            typing_thm([], tp_tm, body_ty),
            th, ty_eq,
        ),
    )


def _other_side_ty(eq: type_eq_thm, ty, ctx: str):
    """Mirror of fusion_dhol._other_side, kept local to avoid a private
    import."""
    if type_eq(eq._lhs, ty):
        return eq._rhs
    if type_eq(eq._rhs, ty):
        return eq._lhs
    raise HolError(
        f"{ctx}: bridge {_pp_ty(eq._lhs)} == {_pp_ty(eq._rhs)} "
        f"does not connect {_pp_ty(ty)}"
    )


def TY_SYM(eq: type_eq_thm) -> type_eq_thm:
    """`Γ |- A == B` → `Γ |- B == A`. Re-exported from the kernel."""
    from fusion_dhol import TY_SYM as _TY_SYM
    return _TY_SYM(eq)


# --- TM_CONG_HETERO_AX ----------------------------------------------------
# Term-side congruence with a heterogeneous body-type bridge for a
# *staged constant*. Because the structural rule is parameterised over
# the constant's Φ, the axiom is built lazily per-constant on first use
# (and cached). The shape is uniform across constants: it asserts that,
# given the homogeneous equation `c(σ_l) = c(σ_l)` (the kernel TM_CONG_BASE
# trivially produces this via dual-σ when both sides match) and a
# cod_eq bridge to A[σ_r], the equation `c(σ_l) = c(σ_r)` holds at
# A[σ_l] with the cod_eq's asl absorbed.
#
# The kernel does the heavy structural σ-dual work; this axiom only
# provides the conclusion the structural rule used to produce inline.

_tm_cong_axiom_cache: dict = {}


def _build_tm_cong_hetero_ax(name: str) -> StagedThm:
    """Lazily build the heterogeneous-bridge axiom for staged constant
    `name`. The axiom takes the same σ-dual the kernel TM_CONG_BASE
    consumes plus a `TyEqAssume` bridging the two body-type sides."""
    phi = get_const_phi(name)
    decl_ty = get_const_type(name)
    # Reuse the constant's Φ twice (LHS and RHS sides) with fresh-name
    # mangling, plus per-Var equation Assumes and the body-type
    # TyEqAssume. To keep the axiom shape simple, we ALSO require the
    # constant's declared Φ to be free of Assume / TyEqAssume entries
    # -- only Tyvar / TyopVar / Var slots are supported here.
    for b in phi:
        if not isinstance(b, (Tyvar, TyopVar, Var)):
            raise HolError(
                "TM_CONG_BASE (cod_eq): heterogeneous wrapper only "
                "handles constants with Tyvar/TyopVar/Var Φ slots "
                f"(got {type(b).__name__} in {name}'s Φ)"
            )

    def _suffix(slot, suf):
        if isinstance(slot, Tyvar):
            return Tyvar(slot.name + suf)
        if isinstance(slot, TyopVar):
            params = tuple(
                Var(p.name + suf, _renamed_ty(p.ty, suf, phi))
                for p in slot.params
            )
            return TyopVar(slot.name + suf, params)
        return Var(slot.name + suf, _renamed_ty(slot.ty, suf, phi))

    def _renamed_ty(ty, suf, phi):
        rename_tyvars = [(Tyvar(b.name + suf), Tyvar(b.name))
                         for b in phi if isinstance(b, Tyvar)]
        rename_vars = [
            (Var(b.name + suf, type_subst(rename_tyvars, b.ty)),
             Var(b.name, b.ty))
            for b in phi if isinstance(b, Var)
        ]
        ty1 = type_subst(rename_tyvars, ty)
        ty1 = subst_in_type([(uv, ov) for uv, ov in rename_vars], ty1)
        return _rename_tyops(ty1, suf, phi)

    def _rename_tyops(ty, suf, phi):
        op_names = {b.name for b in phi if isinstance(b, TyopVar)}
        if not op_names:
            return ty
        if isinstance(ty, Tyvar):
            return ty
        if isinstance(ty, Tyapp):
            return Tyapp(
                ty.tyop,
                tuple(_rename_tyops(a, suf, phi) for a in ty.type_args),
                tuple(_rename_tyops_tm(a, suf, phi) for a in ty.term_args),
            )
        if isinstance(ty, Pi):
            return Pi(
                Var(ty.bvar.name, _rename_tyops(ty.bvar.ty, suf, phi)),
                _rename_tyops(ty.body, suf, phi),
            )
        if isinstance(ty, Subtype):
            return Subtype(
                Var(ty.bvar.name, _rename_tyops(ty.bvar.ty, suf, phi)),
                _rename_tyops_tm(ty.predicate, suf, phi),
            )
        if isinstance(ty, TyopApp):
            new_name = ty.name + suf if ty.name in op_names else ty.name
            return TyopApp(
                new_name,
                tuple(_rename_tyops_tm(a, suf, phi) for a in ty.args),
            )
        raise HolError("_rename_tyops: ill-formed type")

    def _rename_tyops_tm(tm, suf, phi):
        op_names = {b.name for b in phi if isinstance(b, TyopVar)}
        var_names = {b.name for b in phi if isinstance(b, Var)}
        if isinstance(tm, Var):
            ty = _rename_tyops(tm.ty, suf, phi)
            new_name = tm.name + suf if tm.name in var_names else tm.name
            return Var(new_name, ty)
        if isinstance(tm, Const):
            return Const(
                tm.name,
                _rename_tyops(tm.ty, suf, phi),
                tuple(_rename_tyops_tm(a, suf, phi) for a in tm.term_args),
            )
        if isinstance(tm, Comb):
            return Comb(
                _rename_tyops_tm(tm.fun, suf, phi),
                _rename_tyops_tm(tm.arg, suf, phi),
            )
        if isinstance(tm, Abs):
            return Abs(
                Var(tm.bvar.name, _rename_tyops(tm.bvar.ty, suf, phi)),
                _rename_tyops_tm(tm.body, suf, phi),
            )
        raise HolError("_rename_tyops_tm: ill-formed term")

    # Build the Φ: original slots renamed with "_L"/"_R" prefix, plus
    # per-Var Assume slots equating the two sides, plus a TyEqAssume
    # for the body type bridge.
    phi_L = [_suffix(b, "_L") for b in phi]
    phi_R = [_suffix(b, "_R") for b in phi]
    # Build the LHS / RHS body types under each side's substitution.
    A_L = _renamed_ty(decl_ty, "_L", phi)
    A_R = _renamed_ty(decl_ty, "_R", phi)
    # Per-Var equation assumptions.
    var_eqs = []
    for orig, sl, sr in zip(phi, phi_L, phi_R):
        if isinstance(orig, Var):
            var_eqs.append(Assume(safe_mk_eq(sl.ty, sl, sr)))
    new_phi = (
        *phi_L, *phi_R, *var_eqs,
        TyEqAssume((), A_L, A_R),
    )
    # Body: c(σ_L) = c(σ_R) tagged at A_L.
    L_term_args = tuple(
        Var(b.name + "_L", _renamed_ty(b.ty, "_L", phi))
        for b in phi if isinstance(b, Var)
    )
    R_term_args = tuple(
        Var(b.name + "_R", _renamed_ty(b.ty, "_R", phi))
        for b in phi if isinstance(b, Var)
    )
    lhs_const = Const(name, A_L, L_term_args)
    rhs_const = Const(name, A_R, R_term_args)
    body = safe_mk_eq(A_L, lhs_const, rhs_const)
    F_th = typing_thm([a.formula for a in var_eqs], body, bool_ty)
    ax = new_axiom(F_th, phi=new_phi)
    _tm_cong_axiom_cache[name] = ax
    return ax


def TM_CONG_BASE(name: str, args: list,
                 cod_eq: type_eq_thm | None = None) -> thm:
    """Term-side congruence for a staged constant. Without ``cod_eq``
    delegates to the (homogeneous) kernel rule. With ``cod_eq``,
    discharges the heterogeneous body-type case via a
    `TM_CONG_HETERO_AX` family axiom (built lazily per constant)."""
    if cod_eq is None:
        return _kernel_TM_CONG_BASE(name, args)
    ax = _tm_cong_axiom_cache.get(name) or _build_tm_cong_hetero_ax(name)
    phi = get_const_phi(name)
    # Walk args (per-slot σ-dual evidence) and split into LHS / RHS σ.
    sigma_L = []
    sigma_R = []
    var_assume_thms = []
    for slot, arg in zip(phi, args):
        if isinstance(slot, Tyvar):
            # arg is type_eq_thm; split into lhs/rhs hol_types.
            sigma_L.append(arg._lhs)
            sigma_R.append(arg._rhs)
        elif isinstance(slot, TyopVar):
            # arg is TypeAbs; used on both sides (symmetric only).
            sigma_L.append(arg)
            sigma_R.append(arg)
        elif isinstance(slot, Var):
            # arg is equation thm; lhs is typing for L, rhs for R.
            tag = _eq_tag(arg._concl)
            sigma_L.append(typing_thm([], _lhs(arg._concl), tag))
            sigma_R.append(typing_thm([], _rhs(arg._concl), tag))
            var_assume_thms.append(arg)
        else:
            raise HolError(
                f"TM_CONG_BASE(cod_eq): unsupported slot kind "
                f"{type(slot).__name__}"
            )
    return interpret(
        ax,
        (*sigma_L, *sigma_R, *var_assume_thms, cod_eq),
    )


# ---------------------------------------------------------------------------
# Smoke test
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("T_DEF      ::", T_DEF)
    print("TRUTH      ::", TRUTH)
    print("AND_DEF    ::", AND_DEF)
    print("IMP_DEF    ::", IMP_DEF)
    print("ETA_AX     ::", ETA_AX)

    # CONJ smoke: from |- T (TRUTH) and |- T, derive |- T /\ T.
    truth_conj = CONJ(TRUTH, TRUTH)
    print("T /\\ T     ::", truth_conj)

    # CONJUNCT1 / CONJUNCT2 round-trip:
    print("CONJUNCT1  ::", CONJUNCT1(truth_conj))
    print("CONJUNCT2  ::", CONJUNCT2(truth_conj))

    # DISCH / MP round-trip: prove |- T ==> T, then MP with |- T.
    T_typing = _T_const_th                          # |- T : bool
    asm_T_thm = ASSUME(T_typing)                    # [T] |- T
    imp_TT = DISCH(T_typing, asm_T_thm)             # |- T ==> T
    print("DISCH      ::", imp_TT)
    mp_TT = MP(imp_TT, TRUTH)                       # |- T
    print("MP         ::", mp_TT)

    # IMP_TYPE: type-level Rule D wrapper.
    print("IMP_TYPE   ::", IMP_TYPE(T_typing, T_typing))

    # ETA: non-dependent. Declare a stub constant g : bool -> bool.
    from fusion_dhol import new_constant, new_type, mk_type
    new_constant("g", mk_arrow(bool_ty, bool_ty))
    g_th = CONST("g")
    g_eta = ETA(g_th)
    print("ETA(g)     ::", g_eta)

    # ETA: fully dependent. Declare nat, vec(n:nat) : tp, and a constant
    # h : Pi(n:nat). vec(n). ETA should give h = (\n:nat. h n) at the
    # dependent Pi -- no more rejection.
    n_ty = Tyapp("nat", (), ())
    new_type("nat", phi=(), witness=("0", n_ty))
    n_var = Var("n", n_ty)
    nil_ty = Tyapp("vec", (), (Const("0", n_ty),))
    new_type("vec", phi=(n_var,), witness=("nil", nil_ty))
    h_ty = Pi(n_var, mk_type("vec", [VAR(n_var)]))
    new_constant("h", h_ty)
    h_th = CONST("h")
    h_eta = ETA(h_th)
    print("ETA(h)     ::", h_eta)

    # PI_CONG_AX: derive Pi(n:nat). bool == Pi(n:nat). bool from
    # nat == nat and bool == bool (both via TY_REFL).
    from fusion_dhol import TY_REFL
    nat_refl = TY_REFL(n_ty)
    bool_refl = TY_REFL(bool_ty)
    pi_eq = TY_CONG_PI(n_var, nat_refl, bool_refl)
    print("TY_CONG_PI ::", pi_eq)

    # MK_COMB heterogeneous: build add_0 0 = 0 to bridge vec(add 0 0)
    # vs vec(0).
    new_constant("add", mk_arrow(n_ty, mk_arrow(n_ty, n_ty)))
    zero_th = CONST("0")
    add_th = CONST("add")
    add_0 = APP(add_th, zero_th)                       # add 0 : nat -> nat
    add_0_0 = APP(add_0, zero_th)                      # add 0 0 : nat
    # axiom: |- add 0 0 = 0
    add_eq_0_ax = new_axiom(typing_thm([], safe_mk_eq(n_ty, add_0_0._tm, zero_th._tm), bool_ty))
    add_eq_0 = interpret(add_eq_0_ax, ())
    # type bridge vec(add 0 0) == vec(0) via TY_CONG_BASE
    from fusion_dhol import TY_CONG_BASE
    vec_bridge = TY_CONG_BASE("vec", [add_eq_0])
    # Now MK_COMB: f = mkvec : Pi(n:nat). vec n; apply to add_eq_0.
    new_constant("mkvec", Pi(n_var, mk_type("vec", [VAR(n_var)])))
    mkvec_th = CONST("mkvec")
    f_eq = REFL(mkvec_th)                              # |- mkvec = mkvec
    bridged = MK_COMB(f_eq, add_eq_0, cod_eq=vec_bridge)
    print("MK_COMB co ::", bridged)

    # ABS heterogeneous: (\v:vec 0. 0) = (\v:vec(add 0 0). 0)
    body_zero = REFL(zero_th)                          # |- 0 = 0 at nat
    v_at_vec0 = Var("v", mk_type("vec", [zero_th]))
    abs_hetero = ABS(v_at_vec0, body_zero, ty_eq=TY_SYM(vec_bridge))
    print("ABS ty_eq  ::", abs_hetero)

    # TM_CONG_BASE heterogeneous: lift inc(n) = inc(n') across n != n'.
    # inc takes a nat parameter and returns a vec at that nat -- dependent
    # body type, so different σ values produce different body types.
    new_constant("inc", mk_type("vec", [VAR(n_var)]), phi=(n_var,))
    # inc(add 0 0) = inc(0) via TM_CONG_BASE with cod_eq.
    inc_cong = TM_CONG_BASE("inc", [add_eq_0], cod_eq=vec_bridge)
    print("TM_CONG co ::", inc_cong)
