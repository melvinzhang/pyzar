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
    VAR, CONST, LAMBDA, CONV,
    APP as _kernel_APP,
    MK_COMB as _kernel_MK_COMB,
    REFL, ASSUME, BETA, ABS,
    EQ_MP, DEDUCT_ANTISYM_RULE, INST, INST_TYPE,
    EQ_TY_CONV,
    SUBSUME, ST_FORGET,
    TYPE_OF, LHS_TYPING, RHS_TYPING, CONCL_TYPING,
    new_basic_definition, new_axiom, interpret,
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
       →  `Γ |- f a =_B[a/x] f' a'`. `cod_eq` is forwarded to the kernel
       for the dependent-codomain bridge (irreducible). Without `eq`,
       equivalent to kernel MK_COMB."""
    if eq is not None:
        th2 = EQ_TY_CONV(th2, eq)
    return _kernel_MK_COMB(th1, th2, cod_eq=cod_eq)


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
    lam_eq = ABS(_f_var, fpq_eq_fTT)                  # [p, q] |- (\f. f p q) = (\f. f T T)

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
    eta_at = interpret(ETA_AX, (A_ty, B_ty, t_th))
    return SYM(eta_at)


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
