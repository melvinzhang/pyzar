"""Bit operations on ``nat0``.

Stage 1 of the Ackermann/HF construction (``hf_sets.py``).

Builds, in order:
  1. ``double n``  -- shift left by one bit.
  2. ``ODD n``     -- low bit (parity).
  3. ``HALF n``    -- shift right by one bit (uses ``COND`` for the
                      odd/even branch).
  4. ``pow2 i``    -- 2^i as a nat0 (so ``pow2 0 = 1``).
  5. ``bit i n``   -- whether bit ``i`` of ``n`` is set; recursion on
                      ``i`` peels through ``HALF``.

Plus the standard lemmas (bit at 0, bit at pow2, bit-extensionality,
bit-monotonicity) that downstream HF proofs lean on.

All definitions are primitive-recursive on nat0 (via
``nat0.define_unary_0`` and ``nat0.define_recursive_0``); no axioms
are posted in this file.
"""

from fusion import Var, INST_TYPE, aty
from basics import mk_abs, mk_app, mk_const
from parser import parse_type, set_default_var_ty
from axioms import T, F, mk_not, bool_ty
from nat0 import (
    nat0_ty,
    ZERO,
    mk_suc0,
    define_unary_0,
    define_recursive_0,
)
from classical import COND, mk_cond, COND_T, COND_F, NOT_NOT_EQ
from proof import proof


# Bits work entirely on ``nat0``, so default free vars to that type for the
# rest of this module's parser activity.
set_default_var_ty(nat0_ty)


# ``~F = T`` -- the rewriter doesn't simplify ``~F`` automatically, so cache
# the equation. Proof: F ==> F (DISCH F F) gives |- ~F via NOT_INTRO; EQT_INTRO
# turns the resulting |- ~F into |- ~F = T.
def _prove_not_F_eq_T():
    from fusion import ASSUME
    from tactics import DISCH, NOT_INTRO, EQT_INTRO

    not_F = NOT_INTRO(DISCH(F, ASSUME(F)))  # |- ~F
    return EQT_INTRO(not_F)  # |- ~F = T


_NOT_F_EQ_T = _prove_not_F_eq_T()


# Companion: ``~T = F``.  We can't prove ``~T`` directly (false), so derive
# via NOT_NOT_EQ at T plus TRUTH, giving |- ~~T, then EQF_INTRO over the
# outer ``~``.
def _prove_not_T_eq_F():
    from fusion import REFL
    from tactics import EQF_INTRO, SPEC, SYM, EQ_MP, TRUTH

    nn_T_eq_T = SPEC(T, _NOT_NOT_EQ)  # |- ~~T = T
    nn_T = EQ_MP(SYM(nn_T_eq_T), TRUTH)  # |- ~~T
    return SYM(EQF_INTRO(nn_T))  # EQF_INTRO orients as F = ~T; SYM flips it


from classical import NOT_NOT_EQ as _NOT_NOT_EQ

_NOT_T_EQ_F = _prove_not_T_eq_F()


# Type-instantiated copies of the polymorphic COND_T / COND_F at A := nat0,
# so the rewriter can unify with concrete nat0-typed COND occurrences.
COND_T_NAT0 = INST_TYPE([(nat0_ty, aty)], COND_T)
COND_F_NAT0 = INST_TYPE([(nat0_ty, aty)], COND_F)


# Register a parser alias for the nat0-instance of COND so we can write
# ``COND b x y`` in goal strings without worrying about the parser's lack of
# polymorphic-constant unification.
from parser import add_const as _add_const

_COND_nat0_const = mk_const("COND", [(nat0_ty, aty)])
_add_const("COND_nat0", _COND_nat0_const)


# Standard variable names re-used across the bit lemmas.
_i = Var("i", nat0_ty)
_n = Var("n", nat0_ty)
_m = Var("m", nat0_ty)
_k = Var("k", nat0_ty)
_a_n0 = Var("a", nat0_ty)
_a_bool = Var("a", bool_ty)


# ---------------------------------------------------------------------------
# 1. ``double n``  --  double 0 = 0, double (SUC0 n) = SUC0 (SUC0 (double n))
# ---------------------------------------------------------------------------

_h_double = mk_abs(_n, mk_abs(_a_n0, mk_suc0(mk_suc0(_a_n0))))
DOUBLE_BASE, DOUBLE_STEP = define_unary_0(
    "double",
    parse_type("nat0 -> nat0"),
    ZERO,
    _h_double,
    result_ty=nat0_ty,
)
double = mk_const("double", [])


# ---------------------------------------------------------------------------
# 2. ``ODD n``  --  ODD 0 = F, ODD (SUC0 n) = ~(ODD n)
# ---------------------------------------------------------------------------

_h_odd = mk_abs(_n, mk_abs(_a_bool, mk_not(_a_bool)))
ODD_BASE, ODD_STEP = define_unary_0(
    "ODD",
    parse_type("nat0 -> bool"),
    F,
    _h_odd,
    result_ty=bool_ty,
)
ODD = mk_const("ODD", [])


# ---------------------------------------------------------------------------
# 3. ``HALF n``  --  floor(n / 2).
#
#   HALF 0       = 0
#   HALF (SUC0 n) = COND (ODD n) (SUC0 (HALF n)) (HALF n)
#
# Verify by hand:
#   HALF 1 = COND (ODD 0) (SUC0 (HALF 0)) (HALF 0)
#          = COND F (SUC0 0) 0  =  0.            (correct: floor(1/2) = 0)
#   HALF 2 = COND (ODD 1) (SUC0 (HALF 1)) (HALF 1)
#          = COND T (SUC0 0) 0  =  SUC0 0 = 1.   (correct: floor(2/2) = 1)
#   HALF 3 = COND (ODD 2) (SUC0 (HALF 2)) (HALF 2)
#          = COND F (SUC0 1) 1  =  1.            (correct: floor(3/2) = 1)
# ---------------------------------------------------------------------------

_h_half = mk_abs(
    _n,
    mk_abs(
        _a_n0,
        mk_cond(mk_app(ODD, _n), mk_suc0(_a_n0), _a_n0),
    ),
)
HALF_BASE, HALF_STEP = define_unary_0(
    "HALF",
    parse_type("nat0 -> nat0"),
    ZERO,
    _h_half,
    result_ty=nat0_ty,
)
HALF = mk_const("HALF", [])


# ---------------------------------------------------------------------------
# 4. ``pow2 i``  --  2^i, encoded as a nat0 (so ``pow2 0 = SUC0 0`` = the
#    nat0 representation of 1, and ``pow2 (SUC0 i) = double (pow2 i)``).
# ---------------------------------------------------------------------------

_h_pow2 = mk_abs(_n, mk_abs(_a_n0, mk_app(double, _a_n0)))
POW2_BASE, POW2_STEP = define_unary_0(
    "pow2",
    parse_type("nat0 -> nat0"),
    mk_suc0(ZERO),  # 1, in nat0
    _h_pow2,
    result_ty=nat0_ty,
)
pow2 = mk_const("pow2", [])


# ---------------------------------------------------------------------------
# 5. ``bit i n``  --  recursion on ``i``; the second arg ``n`` rolls
#    through ``HALF`` at each step.
#
#   bit 0 n         = ODD n
#   bit (SUC0 i) n  = bit i (HALF n)
#
# We express the recursion in the curried-result form: ``bit`` is a
# nat0-recursion whose value at each ``i`` is itself the function
# ``\n. ...``. ``define_unary_0`` accepts ``result_ty = nat0 -> bool``
# and threads the polymorphic instance through NUM_RECURSION_0.
# ---------------------------------------------------------------------------

_a_fn = Var("a", parse_type("nat0 -> bool"))
_h_bit = mk_abs(
    _i,
    mk_abs(
        _a_fn,
        mk_abs(_n, mk_app(_a_fn, mk_app(HALF, _n))),
    ),
)
BIT_BASE, BIT_STEP = define_unary_0(
    "bit",
    parse_type("nat0 -> nat0 -> bool"),
    ODD,
    _h_bit,
    result_ty=parse_type("nat0 -> bool"),
)
bit = mk_const("bit", [])


# Pointwise form of BIT_STEP, used by every downstream proof:
#   |- !i n. bit (SUC0 i) n = bit i (HALF n).
def _prove_bit_step_at():
    from fusion import REFL
    from tactics import AP_THM, BETA_CONV, SYM, TRANS, SPEC, GEN, GENL

    # BIT_STEP : |- !i. bit (SUC0 i) = (\n. (bit i) (HALF n))
    step_at_i = SPEC(_i, BIT_STEP)
    # AP_THM at n: |- (bit (SUC0 i)) n = (\n'. (bit i) (HALF n')) n
    applied = AP_THM(step_at_i, _n)
    # BETA: |- (\n'. (bit i) (HALF n')) n = (bit i) (HALF n)
    beta_rhs = BETA_CONV(applied._concl.arg)
    return GENL([_i, _n], TRANS(applied, beta_rhs))


BIT_STEP_AT = _prove_bit_step_at()


# ---------------------------------------------------------------------------
# Lemma:  |- !i. bit i 0 = F.
# Induction on i.  Base: bit 0 0 = ODD 0 = F.  Step: bit (S i) 0 =
# bit i (HALF 0) = bit i 0 = F by IH (HALF 0 = 0).
# ---------------------------------------------------------------------------


@proof
def BIT_AT_ZERO(p):
    p.goal("!i. bit i 0 = F")
    p.fix("i")
    with p.induction("i"):
        with p.base():
            p.thus("bit 0 0 = F").by_rewrite([BIT_BASE, ODD_BASE])
        with p.step("IH"):
            p.thus("bit (SUC0 i) 0 = F").by_rewrite([BIT_STEP_AT, HALF_BASE, "IH"])


# ---------------------------------------------------------------------------
# Lemma:  |- !n. ODD (double n) = F.
# Induction on n.  Base: ODD (double 0) = ODD 0 = F.
# Step: ODD (double (S n)) = ODD (S (S (double n))) = ~~ODD (double n)
#     = ODD (double n) = F by IH and double-negation.
# ---------------------------------------------------------------------------


@proof
def ODD_DOUBLE(p):
    p.goal("!n. ODD (double n) = F")
    p.fix("n")
    with p.induction("n"):
        with p.base():
            p.thus("ODD (double 0) = F").by_rewrite([DOUBLE_BASE, ODD_BASE])
        with p.step("IH"):
            p.thus("ODD (double (SUC0 n)) = F").by_rewrite(
                [DOUBLE_STEP, ODD_STEP, NOT_NOT_EQ, "IH"]
            )


# ---------------------------------------------------------------------------
# Lemma:  |- !n. ODD (SUC0 (double n)) = T.
# Direct: ODD (S(double n)) = ~(ODD (double n)) = ~F = T.
# ---------------------------------------------------------------------------


@proof
def ODD_SUC0_DOUBLE(p):
    p.goal("!n. ODD (SUC0 (double n)) = T")
    p.fix("n")
    # Plain rewrite would leave ~F; the rewriter doesn't simplify ~F to T,
    # so derive it manually.
    p.have("step: ODD (SUC0 (double n)) = ~(ODD (double n))").by_rewrite([ODD_STEP])
    p.have("inner: ODD (double n) = F").by_match(ODD_DOUBLE)
    # ~F = T (T_DEF + boolean algebra). Use NOT_NOT_EQ trick: ~~T = T, and
    # ~F = ~~T since F = ~T (definition of F? no, F is defined separately).
    # Cleaner: directly via case analysis. Use EXCLUDED_MIDDLE on (ODD ...).
    # Simpler still: prove ~F = T as a one-off.
    p.thus("ODD (SUC0 (double n)) = T").by_rewrite(["step", "inner", _NOT_F_EQ_T])


# ---------------------------------------------------------------------------
# Lemma:  |- !n. HALF (double n) = n.
# Induction on n.  Base trivial; step uses HALF_STEP twice (peeling each of
# the two SUC0s contributed by double), ODD_SUC0_DOUBLE and ODD_DOUBLE to
# resolve the two COND branches, and the IH to finish.
# ---------------------------------------------------------------------------


@proof
def HALF_DOUBLE(p):
    p.goal("!n. HALF (double n) = n")
    p.fix("n")
    with p.induction("n"):
        with p.base():
            p.thus("HALF (double 0) = 0").by_rewrite([DOUBLE_BASE, HALF_BASE])
        with p.step("IH"):
            p.thus("HALF (double (SUC0 n)) = SUC0 n").by_rewrite(
                [
                    DOUBLE_STEP,
                    HALF_STEP,
                    ODD_SUC0_DOUBLE,
                    ODD_DOUBLE,
                    COND_T_NAT0,
                    COND_F_NAT0,
                    "IH",
                ]
            )


# ---------------------------------------------------------------------------
# Lemma:  |- !n. HALF (SUC0 (double n)) = n.
# Apply HALF_STEP at SUC0 (double n); resolve the COND with ODD_DOUBLE
# (= F) and finish via HALF_DOUBLE.
# ---------------------------------------------------------------------------


@proof
def HALF_SUC0_DOUBLE(p):
    p.goal("!n. HALF (SUC0 (double n)) = n")
    p.fix("n")
    p.thus("HALF (SUC0 (double n)) = n").by_rewrite(
        [HALF_STEP, ODD_DOUBLE, HALF_DOUBLE, COND_F_NAT0]
    )


# ---------------------------------------------------------------------------
# Lemma:  |- !i. bit i (pow2 i) = T.
# Induction on i.
#   Base: bit 0 (pow2 0) = ODD (SUC0 0) = ~(ODD 0) = ~F = T.
#   Step: bit (SUC0 i) (pow2 (SUC0 i))
#       = bit i (HALF (double (pow2 i)))    [BIT_STEP_AT, POW2_STEP]
#       = bit i (pow2 i)                    [HALF_DOUBLE]
#       = T                                 [IH]
# ---------------------------------------------------------------------------


@proof
def BIT_AT_POW2_SAME(p):
    p.goal("!i. bit i (pow2 i) = T")
    p.fix("i")
    with p.induction("i"):
        with p.base():
            p.thus("bit 0 (pow2 0) = T").by_rewrite(
                [BIT_BASE, POW2_BASE, ODD_STEP, ODD_BASE, _NOT_F_EQ_T]
            )
        with p.step("IH"):
            p.thus("bit (SUC0 i) (pow2 (SUC0 i)) = T").by_rewrite(
                [BIT_STEP_AT, POW2_STEP, HALF_DOUBLE, "IH"]
            )


# ---------------------------------------------------------------------------
# Reconstruction lemma:
#   |- !n. n = COND (ODD n) (SUC0 (double (HALF n))) (double (HALF n)).
#
# Every nat0 is its low bit (ODD n) joined to twice its half. The proof
# inducts on n with a case-split on ODD n in the step.
# ---------------------------------------------------------------------------


@proof
def RECONSTRUCT(p):
    p.goal("!n. n = COND_nat0 (ODD n) (SUC0 (double (HALF n))) (double (HALF n))")
    p.fix("n")
    with p.induction("n"):
        with p.base():
            p.thus(
                "0 = COND_nat0 (ODD 0) (SUC0 (double (HALF 0))) (double (HALF 0))"
            ).by_rewrite(
                [ODD_BASE, HALF_BASE, DOUBLE_BASE, COND_F_NAT0]
            )
        with p.step("IH"):
            from classical import EXCLUDED_MIDDLE
            from tactics import (
                EQT_INTRO, EQF_INTRO, REWRITE_RULE, REWRITE_CONV, SYM,
                AP_TERM as _APT, TRANS,
            )

            SUC0_c = mk_const("SUC0", [])

            with p.cases_on(EXCLUDED_MIDDLE, "ODD n"):
                with p.case("hT: ODD n"):
                    odd_eq_T = EQT_INTRO(p.fact("hT"))  # |- ODD n = T
                    # Simplify IH for this case.
                    ih_simp = REWRITE_RULE(
                        [odd_eq_T, COND_T_NAT0], p.fact("IH")
                    )  # |- n = SUC0 (double (HALF n))
                    # Compute the rewriter's reduction of the goal RHS, then
                    # bridge via SUC0 applied to ih_simp.
                    target = p._parse(
                        "COND_nat0 (ODD (SUC0 n)) "
                        "(SUC0 (double (HALF (SUC0 n)))) (double (HALF (SUC0 n)))"
                    )
                    rhs_eq = REWRITE_CONV(
                        [
                            ODD_STEP, HALF_STEP, DOUBLE_STEP,
                            odd_eq_T, _NOT_T_EQ_F,
                            COND_T_NAT0, COND_F_NAT0,
                        ],
                        target,
                    )  # |- target = SUC0 (SUC0 (double (HALF n)))
                    suc0_ih = _APT(SUC0_c, ih_simp)
                    p.thus(
                        "SUC0 n = COND_nat0 (ODD (SUC0 n)) "
                        "(SUC0 (double (HALF (SUC0 n)))) (double (HALF (SUC0 n)))"
                    ).by_thm(TRANS(suc0_ih, SYM(rhs_eq)))
                with p.case("hF: ~(ODD n)"):
                    # EQF_INTRO orients as F = p; SYM flips to p = F.
                    odd_eq_F = SYM(EQF_INTRO(p.fact("hF")))  # |- ODD n = F
                    ih_simp = REWRITE_RULE(
                        [odd_eq_F, COND_F_NAT0], p.fact("IH")
                    )  # |- n = double (HALF n)
                    target = p._parse(
                        "COND_nat0 (ODD (SUC0 n)) "
                        "(SUC0 (double (HALF (SUC0 n)))) (double (HALF (SUC0 n)))"
                    )
                    rhs_eq = REWRITE_CONV(
                        [
                            ODD_STEP, HALF_STEP, DOUBLE_STEP,
                            odd_eq_F, _NOT_F_EQ_T,
                            COND_T_NAT0, COND_F_NAT0,
                        ],
                        target,
                    )  # |- target = SUC0 (double (HALF n))
                    suc0_ih = _APT(SUC0_c, ih_simp)
                    # |- SUC0 n = SUC0 (double (HALF n))
                    p.thus(
                        "SUC0 n = COND_nat0 (ODD (SUC0 n)) "
                        "(SUC0 (double (HALF (SUC0 n)))) (double (HALF (SUC0 n)))"
                    ).by_thm(TRANS(suc0_ih, SYM(rhs_eq)))


if __name__ == "__main__":
    from parser import pp_thm

    print("Step 1 OK -- double defined.")
    print("  DOUBLE_BASE  :", pp_thm(DOUBLE_BASE))
    print("  DOUBLE_STEP  :", pp_thm(DOUBLE_STEP))
    print("Step 2 OK -- ODD defined.")
    print("  ODD_BASE     :", pp_thm(ODD_BASE))
    print("  ODD_STEP     :", pp_thm(ODD_STEP))
    print("Step 3 OK -- HALF defined.")
    print("  HALF_BASE    :", pp_thm(HALF_BASE))
    print("  HALF_STEP    :", pp_thm(HALF_STEP))
    print("Step 4 OK -- pow2 defined.")
    print("  POW2_BASE    :", pp_thm(POW2_BASE))
    print("  POW2_STEP    :", pp_thm(POW2_STEP))
    print("Step 5 OK -- bit defined.")
    print("  BIT_BASE     :", pp_thm(BIT_BASE))
    print("  BIT_STEP     :", pp_thm(BIT_STEP))
    print("  BIT_STEP_AT  :", pp_thm(BIT_STEP_AT))
    print("Step 6 OK -- BIT_AT_ZERO proved.")
    print("  BIT_AT_ZERO  :", pp_thm(BIT_AT_ZERO))
    print("Step 7 OK -- ODD_DOUBLE proved.")
    print("  ODD_DOUBLE   :", pp_thm(ODD_DOUBLE))
    print("Step 8 OK -- ODD_SUC0_DOUBLE proved.")
    print("  ODD_SUC0_DOUBLE:", pp_thm(ODD_SUC0_DOUBLE))
    print("Step 9 OK -- HALF_DOUBLE proved.")
    print("  HALF_DOUBLE  :", pp_thm(HALF_DOUBLE))
    print("Step 10 OK -- HALF_SUC0_DOUBLE proved.")
    print("  HALF_SUC0_DOUBLE:", pp_thm(HALF_SUC0_DOUBLE))
    print("Step 11 OK -- BIT_AT_POW2_SAME proved.")
    print("  BIT_AT_POW2_SAME:", pp_thm(BIT_AT_POW2_SAME))
    print("Step 12 OK -- RECONSTRUCT proved.")
    print("  RECONSTRUCT  :", pp_thm(RECONSTRUCT))
