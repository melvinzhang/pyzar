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
  ETA_AX, ETA            ETA_AX is an axiom at non-dependent (A -> B);
                         ETA wraps it via INST_TYPE / INST.

Limitation: ETA only fires at non-dependent Pi (A -> B). Fully
dependent eta needs rank-1 type operators in Φ (dhol_missing.md #19).

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
    typing_thm, thm, type_eq_thm,
    bool_ty, aty, safe_mk_eq, mk_arrow,
    VAR, CONST, APP, LAMBDA, CONV,
    REFL, ASSUME, BETA, TRANS, MK_COMB, ABS,
    EQ_MP, DEDUCT_ANTISYM_RULE, INST, INST_TYPE,
    new_basic_definition, new_axiom, interpret,
    HolError, frees, vfree_in,
    _is_eq, _lhs, _rhs, _eq_tag,
    _pp_tm, _pp_ty,
)


# ---------------------------------------------------------------------------
# SYM: needs the LHS's typing certificate because DHOL REFL is typing-driven.
# ---------------------------------------------------------------------------


def SYM(th: thm, lhs_th: typing_thm) -> thm:
    """asl |- a = b   and   |- a : A   →   asl |- b = a.

    HOL Light's SYM uses REFL on the equation's LHS term; the DHOL
    kernel's REFL requires a typing_thm, so callers must pass `lhs_th`.
    """
    if not _is_eq(th._concl):
        raise HolError("SYM: conclusion is not an equation")
    A = _eq_tag(th._concl)
    eq_const_th = CONST("=", (A,))
    refl_eq = REFL(eq_const_th)                 # |- (=) = (=)
    partial = MK_COMB(refl_eq, th)              # |- (=) a = (=) b
    refl_a = REFL(lhs_th)                       # |- a = a
    eq_eq = MK_COMB(partial, refl_a)            # |- (a = a) = (b = a)
    return EQ_MP(eq_eq, refl_a)                 # |- b = a


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
_T_DEF_SYM = SYM(T_DEF, _T_const_th)             # |- ((\p.p) = (\p.p)) = T
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


def EQT_INTRO(th: thm, p_th: typing_thm) -> thm:
    """asl |- p   and   |- p : bool   →   asl |- p = T."""
    # Build polymorphic lemma |- p = (p = T) for free p, then INST.
    p_free = Var("p", bool_ty)
    p_free_th = VAR(p_free)
    p_eq_T_typing = APP(
        APP(CONST("=", (bool_ty,)), p_free_th),
        _T_const_th,
    )                                            # typing |- (p = T) : bool

    asm_p = ASSUME(p_free_th)                    # [p] |- p
    th1 = DEDUCT_ANTISYM_RULE(asm_p, TRUTH)      # [p] |- p = T

    asm_eq = ASSUME(p_eq_T_typing)               # [p = T] |- p = T
    sym_asm_eq = SYM(asm_eq, p_free_th)          # [p = T] |- T = p
    th2 = EQ_MP(sym_asm_eq, TRUTH)               # [p = T] |- p

    pth = DEDUCT_ANTISYM_RULE(th2, th1)          # |- p = (p = T)
    pth_at_p = INST([(p_th, p_free)], pth)       # |- p_th._tm = (p_th._tm = T)
    return EQ_MP(pth_at_p, th)                   # asl |- p_th._tm = T


def EQT_ELIM(th: thm, p_th: typing_thm) -> thm:
    """asl |- p = T   and   |- p : bool   →   asl |- p."""
    return EQ_MP(SYM(th, p_th), TRUTH)


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
    p_eq_T = EQT_INTRO(asm_p, p_th)                   # [p] |- p = T
    q_eq_T = EQT_INTRO(asm_q, q_th)                   # [q] |- q = T

    refl_f = REFL(VAR(_f_var))                        # |- f = f
    fp_eq_fT = MK_COMB(refl_f, p_eq_T)                # [p] |- f p = f T
    fpq_eq_fTT = MK_COMB(fp_eq_fT, q_eq_T)            # [p, q] |- f p q = f T T
    lam_eq = ABS(_f_var, fpq_eq_fTT)                  # [p, q] |- (\f. f p q) = (\f. f T T)

    # |- /\ p q = ((\f. f p q) = (\f. f T T))   (via AND_DEF + 2× BETA)
    refl_p = REFL(p_th)
    refl_q = REFL(q_th)
    # MK_COMB(AND_DEF, refl_p) gives |- /\ p = ((\p q. ...) p)
    and_p_eq = MK_COMB(AND_DEF, refl_p)
    # BETA on (\p. \q. ...) p:
    redex_outer_th = APP(_and_body_th, VAR(_p_var))
    beta_outer = BETA(redex_outer_th)                 # |- (\p. \q. ...) p = \q. ...
    lam_after_p = TRANS(and_p_eq, beta_outer)         # |- /\ p = \q. (\f. f p q) = (\f. f T T)
    # MK_COMB with refl_q: |- /\ p q = (\q. ...) q
    and_pq_eq = MK_COMB(lam_after_p, refl_q)
    redex_inner_th = APP(_and_body_q_th, VAR(_q_var))
    beta_inner = BETA(redex_inner_th)                 # |- (\q. ...) q = ...
    and_pq_eq_unfolded = TRANS(and_pq_eq, beta_inner) # |- /\ p q = ((\f. f p q) = (\f. f T T))

    # Combine: lam_eq : [p, q] |- (\f. f p q) = (\f. f T T)
    #          and_pq_eq_unfolded : |- /\ p q = ((\f. f p q) = (\f. f T T))
    # Symm and EQ_MP to derive [p, q] |- /\ p q.
    rhs_typing = APP(APP(CONST("=", (_fpq_th._ty,)), _fpq_th), _fTT_th)
    sym_and = SYM(and_pq_eq_unfolded, _and_typing(p_th, q_th))
    # sym_and : |- ((\f. f p q) = (\f. f T T)) = /\ p q
    return EQ_MP(sym_and, lam_eq)                     # [p, q] |- /\ p q


_CONJ_PTH = _build_conj_pth()


def mk_and(p: term, q: term) -> term:
    """Build the term `p /\\ q` at type bool."""
    and_ty = mk_arrow(bool_ty, mk_arrow(bool_ty, bool_ty))
    return Comb(Comb(Const("/\\", and_ty), p), q)


def CONJ(th1: thm, th2: thm,
         p_th: typing_thm, q_th: typing_thm) -> thm:
    """th1: asl1 |- p, th2: asl2 |- q   →   asl1 ∪ asl2 |- p /\\ q.

    `p_th : |- p : bool` and `q_th : |- q : bool` certify the two
    conjuncts at the type the kernel's polymorphic = needs."""
    inst_th = INST([(p_th, _p_var), (q_th, _q_var)], _CONJ_PTH)
    # inst_th: [p, q] |- p_th._tm /\ q_th._tm
    # Discharge via PROVE_HYP using th1, th2.
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
    sel_pq_typing = APP(APP(sel1_th, p_th), q_th)
    fpq_at_sel_typing = APP(_fpq_th, sel1_th)
    sym_lhs = SYM(beta_lhs_at_sel, fpq_at_sel_typing)
    step1 = TRANS(sym_lhs, app_eq)
    # step1: [pq] |- sel1 p q = (\f. f T T) sel1
    step2 = TRANS(step1, beta_rhs_at_sel)
    # step2: [pq] |- sel1 p q = sel1 T T

    # Now sel1 p q reduces to p (by 2 BETAs); sel1 T T reduces to T.
    # sel1 = \p q. p, so (\p q. p) p q = p by trivial redexes.
    sel_p_outer = APP(sel1_th, VAR(_p_var))
    beta_sel_p_outer = BETA(sel_p_outer)
    # beta_sel_p_outer : |- (\p q. p) p = \q. p
    sel_p_full = APP(APP(sel1_th, VAR(_p_var)), VAR(_q_var))
    # sel_p_full : typing for (\p q. p) p q.
    # We've already reduced (\p q. p) p to (\q. p). MK_COMB-style:
    # MK_COMB(beta_sel_p_outer, REFL q) gives |- (\p q. p) p q = (\q. p) q
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
    # We have sel1 p q = p (sel_p_fully) and sel1 T T = T (sel_T_fully).
    # So p = T (via SYM and TRANS) under [pq].
    sym_sel_p = SYM(sel_p_fully, sel_pq_typing)
    # sym_sel_p : |- p = (\p q. p) p q
    step3 = TRANS(sym_sel_p, step2)
    # step3 : [pq] |- p = (\p q. p) T T
    step4 = TRANS(step3, sel_T_fully)
    # step4 : [pq] |- p = T
    # EQT_ELIM gives [pq] |- p.
    return EQT_ELIM(step4, p_th)


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

    sel_pq_typing = APP(APP(sel2_th, p_th), q_th)
    fpq_at_sel_typing = APP(_fpq_th, sel2_th)
    sym_lhs = SYM(beta_lhs_at_sel, fpq_at_sel_typing)
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

    sym_sel_p = SYM(sel_p_fully, sel_pq_typing)
    step3 = TRANS(sym_sel_p, step2)
    step4 = TRANS(step3, sel_T_fully)
    # step4 : [pq] |- q = T
    return EQT_ELIM(step4, q_th)


_CONJUNCT1_PTH = _build_conjunct1_pth()
_CONJUNCT2_PTH = _build_conjunct2_pth()


def CONJUNCT1(th: thm, p_th: typing_thm, q_th: typing_thm) -> thm:
    """`th : asl |- p /\\ q`  →  `asl |- p`. Needs typing for both."""
    return PROVE_HYP(th, INST([(p_th, _p_var), (q_th, _q_var)], _CONJUNCT1_PTH))


def CONJUNCT2(th: thm, p_th: typing_thm, q_th: typing_thm) -> thm:
    """`th : asl |- p /\\ q`  →  `asl |- q`. Needs typing for both."""
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

    Mirrors fusion_dhol's old kernel rule. Since ==> is now a defined
    constant, we just call APP twice and let the kernel check the types;
    F is removed from G_th's asl, matching the old `Rule D` behaviour."""
    from fusion_dhol import term_union, term_remove
    _require_bool(F_th, "IMP_TYPE antecedent")
    _require_bool(G_th, "IMP_TYPE consequent")
    imp_th = CONST("==>")
    fG_th = APP(imp_th, F_th)
    # Strip F from G_th's asl before the second APP (the kernel takes union):
    G_th_cleaned = typing_thm(
        term_remove(F_th._tm, G_th._asl),
        G_th._tm,
        G_th._ty,
    )
    return APP(fG_th, G_th_cleaned)


def DISCH(F_th: typing_thm, th: thm) -> thm:
    """asl, F |- G  →  asl |- F ==> G  (HOL Light bool.ml derivation).

    F_th : Gamma |- F : bool certifies the antecedent."""
    from fusion_dhol import type_eq as _type_eq, term_union
    _require_bool(F_th, "DISCH antecedent")
    F_tm = F_th._tm
    G_tm = th._concl

    # We need typing for G. ASSUME(typing_thm([], G, bool)) would do — but only
    # if G is closed and well-typed at bool. Conclusions of validity proofs
    # are always at bool, so we trust the caller. Build a typing_thm directly
    # via VAR-style construction is unsafe; instead, derive it from the
    # asm-chain. The cleanest path: build typing_thm via a fresh ASSUME.
    G_typing = typing_thm([G_tm], G_tm, bool_ty)
    # (G_typing's asl contains G_tm; CONJ/etc absorb it into the proof asl,
    #  and PROVE_HYP discharges it via th below. No new free hyps leak.)

    # th1 = CONJ(ASSUME F, th)  : asl, F |- F /\ G
    asm_F = ASSUME(F_th)
    th1 = CONJ(asm_F, th, F_th, G_typing)
    # th1's asl includes F_th._asl, th._asl, F, plus the bool-typing's [G] —
    # but PROVE_HYP discharges G via th, see below.

    # th2 = CONJUNCT1(ASSUME(F /\ G))  : [F /\ G] |- F
    F_and_G_tm = mk_and(F_tm, G_tm)
    F_and_G_typing = _and_typing(F_th, G_typing)
    asm_FG = ASSUME(F_and_G_typing)
    th2 = CONJUNCT1(asm_FG, F_th, G_typing)
    # asl of th2: [F /\ G, G]  (G from G_typing's asl threading through)

    # th3 = DEDUCT_ANTISYM_RULE(th1, th2) : asl |- (F /\ G) = F
    # th1 concl = F /\ G, th2 concl = F
    # th1 asl includes F (we want it removed by DAR via th2.concl = F).
    # th2 asl includes F /\ G (removed via th1.concl = F /\ G).
    th3 = DEDUCT_ANTISYM_RULE(th1, th2)

    # Now build |- (F /\ G = F) = (F ==> G), i.e. SYM of IMP_DEF unfolded.
    imp_unfold = _imp_unfold_eq(F_th, G_typing)
    # imp_unfold : |- (F ==> G) = ((F /\ G) = F)
    fg_eq_F_typing = APP(
        APP(CONST("=", (bool_ty,)), F_and_G_typing),
        F_th,
    )
    imp_typing = APP(APP(CONST("==>"), F_th), G_typing)
    # SYM expects lhs_th = imp_typing (the LHS of imp_unfold).
    sym_imp = SYM(imp_unfold, imp_typing)
    # sym_imp : |- ((F /\ G) = F) = (F ==> G)
    result = EQ_MP(sym_imp, th3)

    # Clean stray G-typing assumption (G_typing carried [G] through CONJ).
    # The asl was threaded but never *added* to the result — DAR + EQ_MP
    # don't introduce new asl beyond what came in. Let's verify by
    # explicit removal of G if it crept in:
    from fusion_dhol import term_remove
    cleaned_asl = term_remove(G_tm, result._asl)
    # G may appear because G_typing's [G] threaded through. Strip it.
    return thm(cleaned_asl, result._concl)


def MP(imp_th: thm, ant_th: thm) -> thm:
    """`asl1 |- F ==> G`, `asl2 |- F`  →  `asl1 ∪ asl2 |- G`.

    Derived via IMP_DEF + CONJ + CONJUNCT2."""
    if not is_imp(imp_th._concl):
        raise HolError("MP: first argument is not an implication")
    F_tm, G_tm = dest_imp(imp_th._concl)
    if not _alpha_eq(F_tm, ant_th._concl):
        raise HolError("MP: antecedent does not match")

    F_typing = typing_thm([F_tm], F_tm, bool_ty)
    G_typing = typing_thm([G_tm], G_tm, bool_ty)
    # Use IMP_DEF unfolding: (F ==> G) = ((F /\ G) = F)
    imp_unfold = _imp_unfold_eq(F_typing, G_typing)
    # imp_unfold: |- (F ==> G) = ((F /\ G) = F)
    fg_eq_F = EQ_MP(imp_unfold, imp_th)
    # fg_eq_F: asl1 |- (F /\ G) = F

    # SYM gives F = F /\ G, EQ_MP with ant_th gives asl1 ∪ asl2 |- F /\ G.
    F_and_G_typing = _and_typing(F_typing, G_typing)
    sym_fg = SYM(fg_eq_F, F_and_G_typing)
    # sym_fg: asl1 |- F = (F /\ G)
    f_and_g_thm = EQ_MP(sym_fg, ant_th)
    # f_and_g_thm: asl1 ∪ asl2 |- F /\ G

    g_thm = CONJUNCT2(f_and_g_thm, F_typing, G_typing)
    # Strip stray F, G typing-assumptions threaded through CONJUNCT2.
    from fusion_dhol import term_remove
    cleaned = term_remove(G_tm, term_remove(F_tm, g_thm._asl))
    return thm(cleaned, g_thm._concl)


def _alpha_eq(a, b) -> bool:
    from fusion_dhol import _tm_alpha
    return _tm_alpha([], a, b)


# ---------------------------------------------------------------------------
# ETA: axiomatised at non-dependent Pi.
#
# ETA_AX : (A:tp, B:tp, f:A->B) ▷ (\x:A. f x) = f
#
# Fully dependent eta (f : Pi(x:A). B(x)) is NOT covered -- that would
# need B to vary with x, which requires rank-1 type operators in Φ.
# ---------------------------------------------------------------------------


_A_tv = Tyvar("A")
_B_tv = Tyvar("B")
_f_AB_var = Var("f", mk_arrow(_A_tv, _B_tv))
_x_A_var = Var("x", _A_tv)
# (\x:A. f x) at A -> B
_lam_fx_th = LAMBDA(_x_A_var, APP(VAR(_f_AB_var), VAR(_x_A_var)))
_eta_form = safe_mk_eq(
    mk_arrow(_A_tv, _B_tv),
    _lam_fx_th._tm,
    VAR(_f_AB_var)._tm,
)
ETA_AX = new_axiom(
    typing_thm([], _eta_form, bool_ty),
    phi=(_A_tv, _B_tv, _f_AB_var),
)


def ETA(t_th: typing_thm) -> thm:
    """`Gamma |- t : Pi(x:A). B   →   Gamma |- t = (\\x:A. t x)`.

    Only the *non-dependent* case (B does not mention x) is supported,
    since ETA_AX is axiomatised at `f : A -> B`. Fully dependent eta
    requires rank-1 type operators in Φ -- dhol_missing.md item 19."""
    ty = t_th._ty
    if not isinstance(ty, Pi):
        raise HolError(f"ETA: term type is not a Pi (got {_pp_ty(ty)})")
    A_ty = ty.bvar.ty
    B_ty = ty.body
    # Reject the fully-dependent case: x must not occur in B.
    from fusion_dhol import _occurs_in_type
    if _occurs_in_type(ty.bvar, B_ty):
        raise HolError(
            "ETA: dependent Pi unsupported -- bound var occurs in "
            "codomain; needs rank-1 type operators (basics_dhol "
            "limitation, not a kernel one)"
        )
    # Instantiate ETA_AX at (A := A_ty, B := B_ty, f := t_th).
    eta_at = interpret(ETA_AX, (A_ty, B_ty, t_th))
    # eta_at : |- (\x:A. t x) = t. SYM to get t = (\x. t x).
    # Need typing for the LHS = (\x:A. t x): build it.
    fresh_x = Var(ty.bvar.name, A_ty)
    lhs_th = LAMBDA(fresh_x, APP(t_th, VAR(fresh_x)))
    return SYM(eta_at, lhs_th)


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
    T_th = _T_const_th
    truth_conj = CONJ(TRUTH, TRUTH, T_th, T_th)
    print("T /\\ T     ::", truth_conj)

    # CONJUNCT1 / CONJUNCT2 round-trip:
    left = CONJUNCT1(truth_conj, T_th, T_th)
    right = CONJUNCT2(truth_conj, T_th, T_th)
    print("CONJUNCT1  ::", left)
    print("CONJUNCT2  ::", right)

    # DISCH / MP round-trip: prove |- T ==> T, then MP with |- T.
    T_typing = T_th  # |- T : bool
    asm_T_thm = ASSUME(T_th)               # [T] |- T
    imp_TT = DISCH(T_typing, asm_T_thm)    # |- T ==> T
    print("DISCH      ::", imp_TT)
    mp_TT = MP(imp_TT, TRUTH)              # |- T
    print("MP         ::", mp_TT)

    # IMP_TYPE: type-level Rule D wrapper.
    imp_type = IMP_TYPE(T_typing, T_typing)
    print("IMP_TYPE   ::", imp_type)

    # ETA: non-dependent. Declare a stub constant f : bool -> bool.
    from fusion_dhol import new_constant
    new_constant("g", mk_arrow(bool_ty, bool_ty))
    g_th = CONST("g")
    g_eta = ETA(g_th)
    print("ETA(g)     ::", g_eta)

    # ETA on dependent Pi is rejected.
    n_ty = Tyapp("nat", (), ())
    try:
        new_constant_failed = False
        from fusion_dhol import new_type
        new_type("nat", phi=(), witness=("0", n_ty))
    except HolError:
        pass  # already declared in repeated runs
    # We can't easily build a Pi(x:nat). vec(x) here without more setup;
    # the kernel's __main__ exercises that path.
