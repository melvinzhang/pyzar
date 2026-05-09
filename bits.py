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
)
from classical import mk_cond, COND_T, COND_F, NOT_NOT_EQ, EXCLUDED_MIDDLE
from proof import proof

# Importing ``nat0_order`` registers the ``nat0`` strong-induction strategy
# with the proof DSL (so ``p.strong_induction("n", "IH")`` works below).
from nat0_order import (
    nat0_lt,  # noqa: F401  -- referenced by the parser via type alias.
    NAT0_LT_SUC0,
    NAT0_LT_TRANS,
    NAT0_LT_SUC0_MONO,
    NAT0_LT_0_SUC0,
    NAT0_LT_SUC0_INSERT,
    NAT0_NOT_LT_ZERO,
    NAT0_NEQ_ZERO_PRED,
    NAT0_LT_SUC0_CASES,
    define_wf_lt,
)
from basics import rand


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
    from tactics import EQF_INTRO, SPEC, SYM, EQ_MP, TRUTH

    nn_T_eq_T = SPEC(T, _NOT_NOT_EQ)  # |- ~~T = T
    nn_T = EQ_MP(SYM(nn_T_eq_T), TRUTH)  # |- ~~T
    return SYM(EQF_INTRO(nn_T))  # EQF_INTRO orients as F = ~T; SYM flips it


from classical import NOT_NOT_EQ as _NOT_NOT_EQ  # noqa: E402 -- needed by _prove_not_T_eq_F above

_NOT_T_EQ_F = _prove_not_T_eq_F()


# Type-instantiated copies of the polymorphic COND_T / COND_F at A := nat0,
# so the rewriter can unify with concrete nat0-typed COND occurrences.
COND_T_NAT0 = INST_TYPE([(nat0_ty, aty)], COND_T)
COND_F_NAT0 = INST_TYPE([(nat0_ty, aty)], COND_F)


# Register a parser alias for the nat0-instance of COND so we can write
# ``COND b x y`` in goal strings without worrying about the parser's lack of
# polymorphic-constant unification.
from parser import add_const as _add_const  # noqa: E402 -- registered after COND_T/F are defined

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
    from tactics import AP_THM, BETA_CONV, TRANS, SPEC, GENL

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
            ).by_rewrite([ODD_BASE, HALF_BASE, DOUBLE_BASE, COND_F_NAT0])
        with p.step("IH"):
            from classical import EXCLUDED_MIDDLE
            from tactics import (
                EQT_INTRO,
                EQF_INTRO,
                REWRITE_RULE,
                REWRITE_CONV,
                SYM,
                AP_TERM as _APT,
                TRANS,
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
                            ODD_STEP,
                            HALF_STEP,
                            DOUBLE_STEP,
                            odd_eq_T,
                            _NOT_T_EQ_F,
                            COND_T_NAT0,
                            COND_F_NAT0,
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
                            ODD_STEP,
                            HALF_STEP,
                            DOUBLE_STEP,
                            odd_eq_F,
                            _NOT_F_EQ_T,
                            COND_T_NAT0,
                            COND_F_NAT0,
                        ],
                        target,
                    )  # |- target = SUC0 (double (HALF n))
                    suc0_ih = _APT(SUC0_c, ih_simp)
                    # |- SUC0 n = SUC0 (double (HALF n))
                    p.thus(
                        "SUC0 n = COND_nat0 (ODD (SUC0 n)) "
                        "(SUC0 (double (HALF (SUC0 n)))) (double (HALF (SUC0 n)))"
                    ).by_thm(TRANS(suc0_ih, SYM(rhs_eq)))


# ---------------------------------------------------------------------------
# Lemma:  |- !j i. ~(i = j) ==> bit i (pow2 j) = F.
#
# The companion to BIT_AT_POW2_SAME; together they characterise
# bit i (pow2 j) entirely. Double induction, outer on j, inner on i.
#
#   j=0, i=0      vacuous (~(0 = 0) is impossible).
#   j=0, i=Si'    bit (Si') (pow2 0) reduces to bit i' 0 = F.
#   j=Sj', i=0    bit 0 (pow2 (Sj')) = ODD (double (pow2 j')) = F.
#   j=Sj', i=Si'  bit (Si') (pow2 (Sj')) = bit i' (pow2 j'); from
#                 ~(Si' = Sj') derive ~(i' = j') by congruence-and-
#                 contradiction, then close via the outer IH at i'.
# ---------------------------------------------------------------------------


@proof
def BIT_AT_POW2_DIFF(p):
    p.goal("!j i. ~(i = j) ==> bit i (pow2 j) = F")
    SUC0_c = mk_const("SUC0", [])
    with p.induction("j"):
        with p.base():
            with p.induction("i"):
                with p.base():
                    p.assume("h: ~(0 = 0)")
                    p.absurd().auto("h")
                with p.step("IH_i_unused"):
                    p.assume("h: ~(SUC0 i = 0)")
                    p.thus("bit (SUC0 i) (pow2 0) = F").by_rewrite(
                        [
                            BIT_STEP_AT,
                            POW2_BASE,
                            HALF_STEP,
                            ODD_BASE,
                            COND_F_NAT0,
                            HALF_BASE,
                            BIT_AT_ZERO,
                        ]
                    )
        with p.step("IH_j"):
            with p.induction("i"):
                with p.base():
                    p.assume("h: ~(0 = SUC0 j)")
                    p.thus("bit 0 (pow2 (SUC0 j)) = F").by_rewrite(
                        [BIT_BASE, POW2_STEP, ODD_DOUBLE]
                    )
                with p.step("IH_i_unused"):
                    p.assume("h: ~(SUC0 i = SUC0 j)")
                    with p.have("hij: ~(i = j)").proof():
                        with p.suppose("heq: i = j"):
                            p.have("seq: SUC0 i = SUC0 j").by_cong(SUC0_c, "heq")
                            p.absurd().by_conj("h", "seq")
                    p.have("bf: bit i (pow2 j) = F").by("IH_j", "i", "hij")
                    p.thus("bit (SUC0 i) (pow2 (SUC0 j)) = F").by_rewrite(
                        [BIT_STEP_AT, POW2_STEP, HALF_DOUBLE, "bf"]
                    )


# ---------------------------------------------------------------------------
# Lemma:  |- !n. nat0_lt (HALF (SUC0 n)) (SUC0 n).
#
# Halving any successor strictly decreases the value. Peano induction on n
# with a case-split on ODD n inside the step:
#   ODD n = T  : HALF (SUC0 (SUC0 n)) collapses to HALF (SUC0 n) (the
#                COND-F branch since ODD (SUC0 n) = ~ODD n = F);
#                HALF (SUC0 n) < SUC0 n by IH, then bumped to
#                SUC0 (SUC0 n) via NAT0_LT_SUC0 + transitivity.
#   ODD n = F  : HALF (SUC0 (SUC0 n)) collapses to SUC0 (HALF (SUC0 n));
#                conclude via NAT0_LT_SUC0_MONO from IH.
# ---------------------------------------------------------------------------


@proof
def HALF_LT_SUC0(p):
    from tactics import EQT_INTRO, EQF_INTRO

    p.goal("!n. nat0_lt (HALF (SUC0 n)) (SUC0 n)")
    p.fix("n")
    with p.induction("n"):
        with p.base():
            p.have("lt0: nat0_lt 0 (SUC0 0)").by(NAT0_LT_SUC0, "0")
            p.thus("nat0_lt (HALF (SUC0 0)) (SUC0 0)").by_rewrite_of(
                "lt0",
                [HALF_STEP, ODD_BASE, COND_F_NAT0, HALF_BASE],
            )
        with p.step("IH"):
            with p.cases_on(EXCLUDED_MIDDLE, "ODD n"):
                with p.case("hO: ODD n"):
                    p.have("hO_eq: ODD n = T").by(EQT_INTRO, "hO")
                    p.have("succ_lt: nat0_lt (SUC0 n) (SUC0 (SUC0 n))").by(
                        NAT0_LT_SUC0, "SUC0 n"
                    )
                    p.have("trans_lt: nat0_lt (HALF (SUC0 n)) (SUC0 (SUC0 n))").by(
                        NAT0_LT_TRANS,
                        "HALF (SUC0 n)",
                        "SUC0 n",
                        "SUC0 (SUC0 n)",
                        "IH",
                        "succ_lt",
                    )
                    p.thus(
                        "nat0_lt (HALF (SUC0 (SUC0 n))) (SUC0 (SUC0 n))"
                    ).by_rewrite_of(
                        "trans_lt",
                        [HALF_STEP, ODD_STEP, "hO_eq", _NOT_T_EQ_F, COND_F_NAT0],
                    )
                with p.case("hNO: ~(ODD n)"):
                    p.have("hNO_eq: ODD n = F").by(EQF_INTRO, "hNO")
                    p.have(
                        "mono_lt: nat0_lt (SUC0 (HALF (SUC0 n))) (SUC0 (SUC0 n))"
                    ).by(
                        NAT0_LT_SUC0_MONO,
                        "HALF (SUC0 n)",
                        "SUC0 n",
                        "IH",
                    )
                    p.thus(
                        "nat0_lt (HALF (SUC0 (SUC0 n))) (SUC0 (SUC0 n))"
                    ).by_rewrite_of(
                        "mono_lt",
                        [HALF_STEP, ODD_STEP, "hNO_eq", _NOT_F_EQ_T, COND_T_NAT0],
                    )


# ---------------------------------------------------------------------------
# Lemma:  |- !n. ~(n = 0) ==> nat0_lt (HALF n) n.
#
# Lifts HALF_LT_SUC0 to arbitrary nonzero n by Peano case analysis: n = 0
# is vacuous (the hypothesis is contradictory); n = SUC0 n' is direct.
# ---------------------------------------------------------------------------


@proof
def HALF_LT_NZ(p):
    p.goal("!n. ~(n = 0) ==> nat0_lt (HALF n) n")
    p.fix("n")
    with p.induction("n"):
        with p.base():
            p.assume("h: ~(0 = 0)")
            p.absurd().auto("h")
        with p.step("_unused"):
            p.assume("h: ~(SUC0 n = 0)")
            p.thus("nat0_lt (HALF (SUC0 n)) (SUC0 n)").by(HALF_LT_SUC0, "n")


# ---------------------------------------------------------------------------
# Lemma:  |- !n. (!i. bit i n = F) ==> n = 0.
#
# An nat0 with all bits clear is zero. Strong induction on n: if n != 0,
# HALF n < n and all bits of HALF n are F (peel via BIT_STEP_AT), so
# the IH gives HALF n = 0; ODD n = F from the bit-at-0 fact; and
# RECONSTRUCT collapses n to double 0 = 0. The n = 0 case is immediate.
# ---------------------------------------------------------------------------


@proof
def ZERO_BITS(p):
    p.goal("!n. (!i. bit i n = F) ==> n = 0")
    with p.strong_induction("n", "IH"):
        p.assume("h: !i. bit i n = F")
        with p.cases_on(EXCLUDED_MIDDLE, "n = 0"):
            with p.case("hz: n = 0"):
                p.thus("n = 0").by_thm(p.fact("hz"))
            with p.case("hnz: ~(n = 0)"):
                p.have("hlt: nat0_lt (HALF n) n").by(HALF_LT_NZ, "n", "hnz")
                with p.have("hh: !i. bit i (HALF n) = F").proof():
                    p.fix("i")
                    p.have("hSi: bit (SUC0 i) n = F").by("h", "SUC0 i")
                    p.thus("bit i (HALF n) = F").by_rewrite_of("hSi", [BIT_STEP_AT])
                p.have("hhalfz: HALF n = 0").by("IH", "HALF n", "hlt", "hh")
                p.have("h0: bit 0 n = F").by("h", "0")
                p.have("hodd: ODD n = F").by_rewrite_of("h0", [BIT_BASE])
                p.have(
                    "recon: n = COND_nat0 (ODD n) "
                    "(SUC0 (double (HALF n))) (double (HALF n))"
                ).by(RECONSTRUCT, "n")
                p.have(
                    "rhs_zero: COND_nat0 (ODD n) "
                    "(SUC0 (double (HALF n))) (double (HALF n)) = 0"
                ).by_rewrite(["hodd", COND_F_NAT0, "hhalfz", DOUBLE_BASE])
                p.thus("n = 0").by_trans("recon", "rhs_zero")


# ---------------------------------------------------------------------------
# BIT_EXTENSIONALITY -- |- !n m. (!i. bit i n = bit i m) ==> n = m.
#
# Strong induction on n with m universally quantified inside the body.
# Two cases:
#   n = 0    : the hypothesis says all bits of m are F; ZERO_BITS finishes.
#   n != 0   : HALF n < n, so the IH applies at HALF n with m' := HALF m.
#              The bit-equality lifted to HALF (peeling BIT_STEP_AT) gives
#              HALF n = HALF m; bit-at-0 gives ODD n = ODD m; RECONSTRUCT
#              both sides finishes via congruence on the COND.
# ---------------------------------------------------------------------------


@proof
def BIT_EXTENSIONALITY(p):
    from tactics import SYM, TRANS

    p.goal("!n m. (!i. bit i n = bit i m) ==> n = m")
    with p.strong_induction("n", "IH"):
        p.fix("m")
        p.assume("h: !i. bit i n = bit i m")
        with p.cases_on(EXCLUDED_MIDDLE, "n = 0"):
            with p.case("hz: n = 0"):
                with p.have("hm_zero: !i. bit i m = F").proof():
                    p.fix("i")
                    p.have("hi: bit i n = bit i m").by("h", "i")
                    p.thus("bit i m = F").by_rewrite(
                        [SYM(p.fact("hi")), "hz", BIT_AT_ZERO]
                    )
                p.have("hm0: m = 0").by(ZERO_BITS, "m", "hm_zero")
                p.thus("n = m").by_thm(TRANS(p.fact("hz"), SYM(p.fact("hm0"))))
            with p.case("hnz: ~(n = 0)"):
                p.have("hlt: nat0_lt (HALF n) n").by(HALF_LT_NZ, "n", "hnz")
                with p.have("hh: !i. bit i (HALF n) = bit i (HALF m)").proof():
                    p.fix("i")
                    p.have("h_si: bit (SUC0 i) n = bit (SUC0 i) m").by("h", "SUC0 i")
                    p.thus("bit i (HALF n) = bit i (HALF m)").by_rewrite_of(
                        "h_si", [BIT_STEP_AT]
                    )
                p.have("hh_eq: HALF n = HALF m").by(
                    "IH", "HALF n", "hlt", "HALF m", "hh"
                )
                p.have("h0: bit 0 n = bit 0 m").by("h", "0")
                p.have("hodd: ODD n = ODD m").by_rewrite_of("h0", [BIT_BASE])
                p.have(
                    "recon_n: n = COND_nat0 (ODD n) "
                    "(SUC0 (double (HALF n))) (double (HALF n))"
                ).by(RECONSTRUCT, "n")
                p.have(
                    "recon_m: m = COND_nat0 (ODD m) "
                    "(SUC0 (double (HALF m))) (double (HALF m))"
                ).by(RECONSTRUCT, "m")
                p.have(
                    "rhs_eq: COND_nat0 (ODD n) "
                    "(SUC0 (double (HALF n))) (double (HALF n)) "
                    "= COND_nat0 (ODD m) "
                    "(SUC0 (double (HALF m))) (double (HALF m))"
                ).by_rewrite(["hodd", "hh_eq"])
                p.thus("n = m").by_thm(
                    TRANS(
                        TRANS(p.fact("recon_n"), p.fact("rhs_eq")),
                        SYM(p.fact("recon_m")),
                    )
                )


# ---------------------------------------------------------------------------
# 6. ``set_bit i n``  --  bit-i flipped to 1, defined recursively in ``i``
#    using only ``ODD`` / ``HALF`` / ``double`` / ``SUC0`` / ``COND`` (no
#    addition required).
#
#   set_bit 0 n         = SUC0 (double (HALF n))                    -- low bit forced 1
#   set_bit (SUC0 i) n  = COND (ODD n)
#                              (SUC0 (double (set_bit i (HALF n))))
#                              (double (set_bit i (HALF n)))
#
# Verify by hand:
#   set_bit 0 4 = SUC0 (double (HALF 4)) = SUC0 (double 2) = SUC0 4 = 5  (bit 0 added: 100 -> 101)
#   set_bit 1 5 = COND T (SUC0 (double (set_bit 0 (HALF 5)))) ...
#               = SUC0 (double (set_bit 0 2)) = SUC0 (double 3) = SUC0 6 = 7  (101 -> 111)
# ---------------------------------------------------------------------------

_a_n0_fn = Var("a", parse_type("nat0 -> nat0"))
_set_bit_base = mk_abs(_n, mk_suc0(mk_app(double, mk_app(HALF, _n))))
_h_set_bit = mk_abs(
    _i,
    mk_abs(
        _a_n0_fn,
        mk_abs(
            _n,
            mk_cond(
                mk_app(ODD, _n),
                mk_suc0(mk_app(double, mk_app(_a_n0_fn, mk_app(HALF, _n)))),
                mk_app(double, mk_app(_a_n0_fn, mk_app(HALF, _n))),
            ),
        ),
    ),
)
SET_BIT_BASE, SET_BIT_STEP = define_unary_0(
    "set_bit",
    parse_type("nat0 -> nat0 -> nat0"),
    _set_bit_base,
    _h_set_bit,
    result_ty=parse_type("nat0 -> nat0"),
)
set_bit = mk_const("set_bit", [])


# Pointwise forms (analogous to BIT_STEP_AT):
#   |- !n. set_bit 0 n = SUC0 (double (HALF n))
#   |- !i n. set_bit (SUC0 i) n
#         = COND_nat0 (ODD n) (SUC0 (double (set_bit i (HALF n))))
#                             (double (set_bit i (HALF n)))
def _prove_set_bit_at():
    from basics import rand
    from tactics import AP_THM, BETA_CONV, TRANS, GEN, GENL, SPEC

    base_at_n = AP_THM(SET_BIT_BASE, _n)  # |- set_bit 0 n = (\n'. ...) n
    base_beta = BETA_CONV(rand(base_at_n._concl))
    base_pointwise = GEN(_n, TRANS(base_at_n, base_beta))

    step_at_i = SPEC(_i, SET_BIT_STEP)  # |- set_bit (SUC0 i) = (\n'. ...)
    step_at_in = AP_THM(step_at_i, _n)
    step_beta = BETA_CONV(rand(step_at_in._concl))
    step_pointwise = GENL([_i, _n], TRANS(step_at_in, step_beta))

    return base_pointwise, step_pointwise


SET_BIT_BASE_AT, SET_BIT_STEP_AT = _prove_set_bit_at()


# ---------------------------------------------------------------------------
# Lemma:  |- !i n. bit i (set_bit i n) = T.
#
# Induction on i.  Base: bit 0 (SUC0 (double (HALF n))) = ODD (SUC0 (double X))
# = T (ODD_SUC0_DOUBLE).  Step: case-split on ODD n; in either branch peel
# BIT_STEP_AT, SET_BIT_STEP_AT, the chosen COND branch and HALF_{SUC0_,}DOUBLE
# to land at bit i (set_bit i (HALF n)), closed by the IH instantiated at
# HALF n.
# ---------------------------------------------------------------------------


@proof
def BIT_AT_SET_BIT_SAME(p):
    from tactics import EQT_INTRO, EQF_INTRO

    p.goal("!i n. bit i (set_bit i n) = T")
    with p.induction("i"):
        with p.base():
            p.fix("n")
            p.thus("bit 0 (set_bit 0 n) = T").by_rewrite(
                [BIT_BASE, SET_BIT_BASE_AT, ODD_SUC0_DOUBLE]
            )
        with p.step("IH"):
            p.fix("n")
            p.have("ih_at: bit i (set_bit i (HALF n)) = T").by("IH", "HALF n")
            with p.cases_on(EXCLUDED_MIDDLE, "ODD n"):
                with p.case("hO: ODD n"):
                    p.have("hO_eq: ODD n = T").by(EQT_INTRO, "hO")
                    p.thus("bit (SUC0 i) (set_bit (SUC0 i) n) = T").by_rewrite(
                        [
                            BIT_STEP_AT,
                            SET_BIT_STEP_AT,
                            "hO_eq",
                            COND_T_NAT0,
                            HALF_SUC0_DOUBLE,
                            "ih_at",
                        ]
                    )
                with p.case("hF: ~(ODD n)"):
                    p.have("hF_eq: ODD n = F").by(EQF_INTRO, "hF")
                    p.thus("bit (SUC0 i) (set_bit (SUC0 i) n) = T").by_rewrite(
                        [
                            BIT_STEP_AT,
                            SET_BIT_STEP_AT,
                            "hF_eq",
                            COND_F_NAT0,
                            HALF_DOUBLE,
                            "ih_at",
                        ]
                    )


# ---------------------------------------------------------------------------
# Lemma:  |- !i j n. ~(i = j) ==> bit j (set_bit i n) = bit j n.
#
# Outer induction on i, inner on j (mirroring BIT_AT_POW2_DIFF).
#   i=0, j=0       : vacuous (~(0 = 0) absurd).
#   i=0, j=Sj'     : bit (Sj') (SUC0 (double (HALF n)))
#                  = bit j' (HALF (SUC0 (double (HALF n))))   [BIT_STEP_AT]
#                  = bit j' (HALF n)                          [HALF_SUC0_DOUBLE]
#                  = bit (Sj') n                              [SYM BIT_STEP_AT]
#   i=Si', j=0     : bit 0 (set_bit (Si') n) = ODD (set_bit ...).
#                    Case-split on ODD n; SET_BIT_STEP_AT + chosen COND branch
#                    + ODD_{SUC0_,}DOUBLE collapses ODD (set_bit ...) to ODD n,
#                    matching the RHS bit 0 n = ODD n.
#   i=Si', j=Sj'   : peel BIT_STEP_AT on both sides, case-split ODD n,
#                    SET_BIT_STEP_AT + COND branch + HALF_{SUC0_,}DOUBLE lands
#                    at bit j' (set_bit i' (HALF n)) = bit j' (HALF n), closed
#                    by IH_i at j', HALF n with ~(i' = j') (derived from the
#                    SUC0-injectivity contrapositive of ~(Si' = Sj')).
# ---------------------------------------------------------------------------


@proof
def BIT_AT_SET_BIT_DIFF(p):
    from tactics import EQT_INTRO, EQF_INTRO

    p.goal("!i j n. ~(i = j) ==> bit j (set_bit i n) = bit j n")
    SUC0_c = mk_const("SUC0", [])
    with p.induction("i"):
        with p.base():
            with p.induction("j"):
                with p.base():
                    p.fix("n")
                    p.assume("h: ~(0 = 0)")
                    p.absurd().auto("h")
                with p.step("IH_j_unused"):
                    p.fix("n")
                    p.assume("h: ~(0 = SUC0 j)")
                    p.thus("bit (SUC0 j) (set_bit 0 n) = bit (SUC0 j) n").by_rewrite(
                        [BIT_STEP_AT, SET_BIT_BASE_AT, HALF_SUC0_DOUBLE]
                    )
        with p.step("IH_i"):
            with p.induction("j"):
                with p.base():
                    p.fix("n")
                    p.assume("h: ~(SUC0 i = 0)")
                    with p.cases_on(EXCLUDED_MIDDLE, "ODD n"):
                        with p.case("hO: ODD n"):
                            p.have("hO_eq: ODD n = T").by(EQT_INTRO, "hO")
                            p.thus("bit 0 (set_bit (SUC0 i) n) = bit 0 n").by_rewrite(
                                [
                                    BIT_BASE,
                                    SET_BIT_STEP_AT,
                                    "hO_eq",
                                    COND_T_NAT0,
                                    ODD_SUC0_DOUBLE,
                                ]
                            )
                        with p.case("hF: ~(ODD n)"):
                            p.have("hF_eq: ODD n = F").by(EQF_INTRO, "hF")
                            p.thus("bit 0 (set_bit (SUC0 i) n) = bit 0 n").by_rewrite(
                                [
                                    BIT_BASE,
                                    SET_BIT_STEP_AT,
                                    "hF_eq",
                                    COND_F_NAT0,
                                    ODD_DOUBLE,
                                ]
                            )
                with p.step("IH_j_unused"):
                    p.fix("n")
                    p.assume("h: ~(SUC0 i = SUC0 j)")
                    with p.have("hij: ~(i = j)").proof():
                        with p.suppose("heq: i = j"):
                            p.have("seq: SUC0 i = SUC0 j").by_cong(SUC0_c, "heq")
                            p.absurd().by_conj("h", "seq")
                    p.have("rec: bit j (set_bit i (HALF n)) = bit j (HALF n)").by(
                        "IH_i", "j", "HALF n", "hij"
                    )
                    with p.cases_on(EXCLUDED_MIDDLE, "ODD n"):
                        with p.case("hO: ODD n"):
                            p.have("hO_eq: ODD n = T").by(EQT_INTRO, "hO")
                            p.thus(
                                "bit (SUC0 j) (set_bit (SUC0 i) n) = bit (SUC0 j) n"
                            ).by_rewrite(
                                [
                                    BIT_STEP_AT,
                                    SET_BIT_STEP_AT,
                                    "hO_eq",
                                    COND_T_NAT0,
                                    HALF_SUC0_DOUBLE,
                                    "rec",
                                ]
                            )
                        with p.case("hF: ~(ODD n)"):
                            p.have("hF_eq: ODD n = F").by(EQF_INTRO, "hF")
                            p.thus(
                                "bit (SUC0 j) (set_bit (SUC0 i) n) = bit (SUC0 j) n"
                            ).by_rewrite(
                                [
                                    BIT_STEP_AT,
                                    SET_BIT_STEP_AT,
                                    "hF_eq",
                                    COND_F_NAT0,
                                    HALF_DOUBLE,
                                    "rec",
                                ]
                            )


# ---------------------------------------------------------------------------
# Bit-monotonicity:  |- !n i. bit i n ==> nat0_lt i n.
#
# Strong induction on n, then case-split on i.
#   i = 0 : bit 0 n = ODD n; assumed true means RECONSTRUCT collapses
#           n = SUC0 (double (HALF n)), and NAT0_LT_0_SUC0 closes the goal.
#   i = SUC0 i' : bit (SUC0 i') n = bit i' (HALF n); the latter implies
#           HALF n != 0 (else bit i' 0 = F), hence n != 0, so HALF_LT_NZ
#           gives nat0_lt (HALF n) n. Strong-IH at HALF n yields
#           nat0_lt i' (HALF n); NAT0_LT_SUC0_INSERT chains the two to
#           nat0_lt (SUC0 i') n.
#
# (The i-induction's IH is unused -- it's a Peano case-split disguised as
# induction, mirroring the BIT_AT_POW2_DIFF idiom.)
# ---------------------------------------------------------------------------


@proof
def BIT_LT(p):
    from fusion import EQ_MP as _EQ_MP
    from tactics import EQT_INTRO, SYM

    p.goal("!n i. bit i n ==> nat0_lt i n")
    with p.strong_induction("n", "IH"):
        with p.induction("i"):
            with p.base():
                p.assume("hb: bit 0 n")
                p.have("hodd: ODD n").by_rewrite_of("hb", [BIT_BASE])
                p.have("hodd_eq: ODD n = T").by(EQT_INTRO, "hodd")
                p.have(
                    "recon: n = COND_nat0 (ODD n) "
                    "(SUC0 (double (HALF n))) (double (HALF n))"
                ).by(RECONSTRUCT, "n")
                p.have("n_eq: n = SUC0 (double (HALF n))").by_rewrite_of(
                    "recon", ["hodd_eq", COND_T_NAT0]
                )
                p.have("lt: nat0_lt 0 (SUC0 (double (HALF n)))").by(
                    NAT0_LT_0_SUC0, "double (HALF n)"
                )
                p.thus("nat0_lt 0 n").by_rewrite_of("lt", [SYM(p.fact("n_eq"))])
            with p.step("IH_i_unused"):
                p.assume("hb: bit (SUC0 i) n")
                p.have("hb_half: bit i (HALF n)").by_rewrite_of("hb", [BIT_STEP_AT])
                with p.have("hh_nz: ~(HALF n = 0)").proof():
                    with p.suppose("hh_z: HALF n = 0"):
                        p.have("bit_at_0: bit i 0 = F").by(BIT_AT_ZERO, "i")
                        p.have("hb_at_0: bit i 0").by_rewrite_of("hb_half", ["hh_z"])
                        p.absurd().by_thm(_EQ_MP(p.fact("bit_at_0"), p.fact("hb_at_0")))
                with p.have("hn_nz: ~(n = 0)").proof():
                    with p.suppose("hn_z: n = 0"):
                        p.have("hh_z: HALF n = 0").by_rewrite_of(HALF_BASE, ["hn_z"])
                        p.absurd().by_conj("hh_nz", "hh_z")
                p.have("half_lt: nat0_lt (HALF n) n").by(HALF_LT_NZ, "n", "hn_nz")
                p.have("i_lt_half: nat0_lt i (HALF n)").by(
                    "IH", "HALF n", "half_lt", "i", "hb_half"
                )
                p.thus("nat0_lt (SUC0 i) n").by(
                    NAT0_LT_SUC0_INSERT,
                    "i",
                    "HALF n",
                    "n",
                    "i_lt_half",
                    "half_lt",
                )


# ---------------------------------------------------------------------------
# 8. ``low_bit n`` and ``clear_low n`` -- canonical low-bit decomposition.
#
#   low_bit n   = COND (n=0) 0 (COND (ODD n) 0 (SUC0 (low_bit (HALF n))))
#               -- position of n's lowest set bit (junk at n = 0).
#   clear_low n = COND (n=0) 0 (COND (ODD n) (double (HALF n))
#                                            (double (clear_low (HALF n))))
#               -- n with its lowest set bit cleared (clear_low 0 = 0).
#
# Both are well-founded recursive on ``nat0_lt`` since the recursive
# call goes to ``HALF n`` and ``HALF_LT_NZ`` gives ``HALF n < n`` for
# ``n != 0`` -- declared via ``define_wf_lt``.
#
# Verify by hand:
#   low_bit 6 = COND F (COND F 0 (SUC0 (low_bit 3)))
#             = SUC0 (COND F (COND T 0 (SUC0 (low_bit 1))))
#             = SUC0 0 = 1.                        (110 -> bit 1 lowest)
#   clear_low 6 = double (clear_low 3)
#               = double (double (HALF 3))   [ODD 3 = T branch]
#               = double (double 1) = 4.           (110 -> 100)
#
# Used by ``hf_to_qhf`` (q_repr.py) to drive the canonical low-bit-first
# Insert_t-tower bridge from HF sets to Q-syntax. The two side conditions
#
#   LOW_BIT_LT   : ~(n = 0) ==> nat0_lt (low_bit n) n
#   CLEAR_LOW_LT : ~(n = 0) ==> nat0_lt (clear_low n) n
#
# (the well-founded-recursion MONO obligation for ``hf_to_qhf``) are
# proved below. The remaining lemmas needed by downstream representability
# proofs (BIT_LOW_BIT, BIT_LOW_BIT_CLEAR_LOW, SET_BIT_LOW_BIT_CLEAR_LOW)
# are added when those proofs land.
# ---------------------------------------------------------------------------


# Helper: F-body for low_bit, clear_low. ``define_wf_lt`` consumes a body
# F : (nat0 -> nat0) -> nat0 -> nat0 along with a MONO proof; we give F a
# name so the recursion equation reads cleanly as ``f n = _F_low_bit f n``.

_F_lcl_ty = parse_type("(nat0 -> nat0) -> nat0 -> nat0")
_F_arg_ty = parse_type("nat0 -> nat0")

from parser import define as _define  # noqa: E402

_LOW_BIT_F_DEF = _define(
    "_low_bit_F",
    _F_lcl_ty,
    "\\f:nat0->nat0. \\n:nat0. "
    "COND_nat0 (n = 0) 0 "
    "(COND_nat0 (ODD n) 0 (SUC0 (f (HALF n))))",
)
_low_bit_F = mk_const("_low_bit_F", [])

_CLEAR_LOW_F_DEF = _define(
    "_clear_low_F",
    _F_lcl_ty,
    "\\f:nat0->nat0. \\n:nat0. "
    "COND_nat0 (n = 0) 0 "
    "(COND_nat0 (ODD n) (double (HALF n)) (double (f (HALF n))))",
)
_clear_low_F = mk_const("_clear_low_F", [])


# Pointwise / beta-normalised forms (analogous to ``_UNION_F_AT`` in
# hf_sets.py): two AP_THM/BETA_CONV peels collapse the ``(\f n. body) f n``
# application to the body.
def _prove_F_at(F_def):
    from tactics import AP_THM, BETA_CONV, TRANS, GENL

    f_var = Var("f", _F_arg_ty)
    n_var = Var("n", nat0_ty)
    th_f = AP_THM(F_def, f_var)
    th_f_eq = TRANS(th_f, BETA_CONV(rand(th_f._concl)))
    th_fn = AP_THM(th_f_eq, n_var)
    th_fn_eq = TRANS(th_fn, BETA_CONV(rand(th_fn._concl)))
    return GENL([f_var, n_var], th_fn_eq)


_LOW_BIT_F_AT = _prove_F_at(_LOW_BIT_F_DEF)
_CLEAR_LOW_F_AT = _prove_F_at(_CLEAR_LOW_F_DEF)


# MONO obligations for ``define_wf_lt``: the body's value at ``n`` only
# depends on ``f``'s value at ``HALF n`` (which is < n for n != 0). The
# n = 0 branch ignores ``f`` entirely; the n != 0 branch funnels through
# the IH (``f (HALF n) = g (HALF n)``).


@proof
def LOW_BIT_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                ==> _low_bit_F f n = _low_bit_F g n."""
    from tactics import EQT_INTRO, EQF_INTRO

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) "
        "==> _low_bit_F f n = _low_bit_F g n",
        types={"f": _F_arg_ty, "g": _F_arg_ty, "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    with p.cases_on(EXCLUDED_MIDDLE, "n = 0"):
        with p.case("hz: n = 0"):
            p.have("hz_eq: (n = 0) = T").by_thm(EQT_INTRO(p.fact("hz")))
            p.thus("_low_bit_F f n = _low_bit_F g n").by_rewrite(
                [_LOW_BIT_F_AT, "hz_eq", COND_T_NAT0]
            )
        with p.case("hnz: ~(n = 0)"):
            p.have("hlt: nat0_lt (HALF n) n").by(HALF_LT_NZ, "n", "hnz")
            p.have("hfg: f (HALF n) = g (HALF n)").by("h", "HALF n", "hlt")
            p.have("hnz_eq: (n = 0) = F").by_thm(EQF_INTRO(p.fact("hnz")))
            p.thus("_low_bit_F f n = _low_bit_F g n").by_rewrite(
                [_LOW_BIT_F_AT, "hnz_eq", COND_F_NAT0, "hfg"]
            )


@proof
def CLEAR_LOW_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                ==> _clear_low_F f n = _clear_low_F g n."""
    from tactics import EQT_INTRO, EQF_INTRO

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) "
        "==> _clear_low_F f n = _clear_low_F g n",
        types={"f": _F_arg_ty, "g": _F_arg_ty, "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    with p.cases_on(EXCLUDED_MIDDLE, "n = 0"):
        with p.case("hz: n = 0"):
            p.have("hz_eq: (n = 0) = T").by_thm(EQT_INTRO(p.fact("hz")))
            p.thus("_clear_low_F f n = _clear_low_F g n").by_rewrite(
                [_CLEAR_LOW_F_AT, "hz_eq", COND_T_NAT0]
            )
        with p.case("hnz: ~(n = 0)"):
            p.have("hlt: nat0_lt (HALF n) n").by(HALF_LT_NZ, "n", "hnz")
            p.have("hfg: f (HALF n) = g (HALF n)").by("h", "HALF n", "hlt")
            p.have("hnz_eq: (n = 0) = F").by_thm(EQF_INTRO(p.fact("hnz")))
            p.thus("_clear_low_F f n = _clear_low_F g n").by_rewrite(
                [_CLEAR_LOW_F_AT, "hnz_eq", COND_F_NAT0, "hfg"]
            )


# Well-founded recursive definitions.
LOW_BIT_DEF, LOW_BIT_REC = define_wf_lt(
    "low_bit",
    parse_type("nat0 -> nat0"),
    _low_bit_F,
    LOW_BIT_MONO,
)
low_bit = mk_const("low_bit", [])

CLEAR_LOW_DEF, CLEAR_LOW_REC = define_wf_lt(
    "clear_low",
    parse_type("nat0 -> nat0"),
    _clear_low_F,
    CLEAR_LOW_MONO,
)
clear_low = mk_const("clear_low", [])


# Direct unfolders: |- !n. low_bit n = body[low_bit, n] (and similarly
# for clear_low). Compose REC (|- !n. f n = _F_f f n) with _F_AT (|- !f n.
# _F f n = body[f, n]) by SPECL + TRANS so the body is in beta-normal form.
def _prove_at_eq(REC_th, F_AT_th, fn_const):
    from tactics import SPEC, SPECL, TRANS, GEN

    n_v = Var("n", nat0_ty)
    fn_at_n = SPEC(n_v, REC_th)
    F_at_n = SPECL([fn_const, n_v], F_AT_th)
    return GEN(n_v, TRANS(fn_at_n, F_at_n))


LOW_BIT_AT = _prove_at_eq(LOW_BIT_REC, _LOW_BIT_F_AT, low_bit)
CLEAR_LOW_AT = _prove_at_eq(CLEAR_LOW_REC, _CLEAR_LOW_F_AT, clear_low)


# ---------------------------------------------------------------------------
# Helper:  |- !a b. nat0_lt a b ==> nat0_lt (double a) (double b).
# Used by CLEAR_LOW_LT in the even-n case where clear_low n unfolds to
# double (clear_low (HALF n)) and the strong-IH at HALF n only gives
# clear_low (HALF n) < HALF n -- the doubling has to be lifted across <.
#
# Induction on b. Base vacuous (NAT0_NOT_LT_ZERO). Step splits a < SUC0 b
# via NAT0_LT_SUC0_CASES into a = b / a < b; both branches reach
# nat0_lt (double a) (SUC0 (SUC0 (double b))) ( = double (SUC0 b) by
# DOUBLE_STEP) via two NAT0_LT_SUC0 hops, with the IH plugged in for the
# strict-< case.
# ---------------------------------------------------------------------------


@proof
def DOUBLE_MONO_LT(p):
    p.goal("!a b. nat0_lt a b ==> nat0_lt (double a) (double b)")
    p.fix("a b")
    with p.induction("b"):
        with p.base():
            p.assume("hlt: nat0_lt a 0")
            p.have("notlt: ~(nat0_lt a 0)").by(NAT0_NOT_LT_ZERO, "a")
            p.absurd().by_conj("notlt", "hlt")
        with p.step("IH"):
            p.assume("hlt: nat0_lt a (SUC0 b)")
            p.have("hop1: nat0_lt (double b) (SUC0 (double b))").by(
                NAT0_LT_SUC0, "double b"
            )
            p.have(
                "hop2: nat0_lt (SUC0 (double b)) (SUC0 (SUC0 (double b)))"
            ).by(NAT0_LT_SUC0, "SUC0 (double b)")
            p.have(
                "hop: nat0_lt (double b) (SUC0 (SUC0 (double b)))"
            ).by(
                NAT0_LT_TRANS,
                "double b",
                "SUC0 (double b)",
                "SUC0 (SUC0 (double b))",
                "hop1",
                "hop2",
            )
            p.have("step_eq: double (SUC0 b) = SUC0 (SUC0 (double b))").by(
                DOUBLE_STEP, "b"
            )
            p.have("cases: a = b \\/ nat0_lt a b").by(
                NAT0_LT_SUC0_CASES, "a", "b", "hlt"
            )
            with p.cases_on("cases"):
                with p.case("heq: a = b"):
                    p.thus("nat0_lt (double a) (double (SUC0 b))").by_rewrite_of(
                        "hop", ["heq", "step_eq"]
                    )
                with p.case("hlt2: nat0_lt a b"):
                    p.have("ih_at: nat0_lt (double a) (double b)").by("IH", "hlt2")
                    p.have(
                        "trans_lt: nat0_lt (double a) (SUC0 (SUC0 (double b)))"
                    ).by(
                        NAT0_LT_TRANS,
                        "double a",
                        "double b",
                        "SUC0 (SUC0 (double b))",
                        "ih_at",
                        "hop",
                    )
                    p.thus("nat0_lt (double a) (double (SUC0 b))").by_rewrite_of(
                        "trans_lt", ["step_eq"]
                    )


# ---------------------------------------------------------------------------
# |- !n. ~(n = 0) ==> nat0_lt (low_bit n) n.
#
# Strong induction on n; case-split on ODD n.
#   ODD n  : low_bit n = 0 (LOW_BIT_AT collapses both COND branches).
#            n != 0 yields n = SUC0 d (NAT0_NEQ_ZERO_PRED), so
#            nat0_lt 0 n via NAT0_LT_0_SUC0.
#   ~ODD n : low_bit n = SUC0 (low_bit (HALF n)).
#            HALF n != 0 (else RECONSTRUCT collapses n to 0, contradiction);
#            HALF n < n by HALF_LT_NZ; strong-IH at HALF n gives
#            low_bit (HALF n) < HALF n; NAT0_LT_SUC0_INSERT chains to
#            SUC0 (low_bit (HALF n)) < n.
# ---------------------------------------------------------------------------


@proof
def LOW_BIT_LT(p):
    from tactics import EQT_INTRO, EQF_INTRO

    p.goal("!n. ~(n = 0) ==> nat0_lt (low_bit n) n")
    with p.strong_induction("n", "IH"):
        p.assume("hnz: ~(n = 0)")
        p.have("hnz_eq: (n = 0) = F").by_thm(EQF_INTRO(p.fact("hnz")))
        # SPEC LOW_BIT_AT at n once, then rewrite-of without re-applying it
        # downstream (its body recurses through ``low_bit (HALF n)``, so
        # leaving it in the rule set blows the rewriter's fixpoint budget).
        p.have(
            "lb_n: low_bit n = COND_nat0 (n = 0) 0 "
            "(COND_nat0 (ODD n) 0 (SUC0 (low_bit (HALF n))))"
        ).by(LOW_BIT_AT, "n")
        with p.cases_on(EXCLUDED_MIDDLE, "ODD n"):
            with p.case("hO: ODD n"):
                p.have("hO_eq: ODD n = T").by_thm(EQT_INTRO(p.fact("hO")))
                p.have("lb_zero: low_bit n = 0").by_rewrite_of(
                    "lb_n", ["hnz_eq", "hO_eq", COND_F_NAT0, COND_T_NAT0]
                )
                p.have("pred: ?d. n = SUC0 d").by(NAT0_NEQ_ZERO_PRED, "n", "hnz")
                p.choose("d", "pred")  # registers d_eq: n = SUC0 d
                p.have("lt_succ: nat0_lt 0 (SUC0 d)").by(NAT0_LT_0_SUC0, "d")
                p.have("lt_n: nat0_lt 0 n").by_rewrite_of("lt_succ", ["d_eq"])
                p.thus("nat0_lt (low_bit n) n").by_rewrite_of("lt_n", ["lb_zero"])
            with p.case("hF: ~(ODD n)"):
                p.have("hF_eq: ODD n = F").by_thm(EQF_INTRO(p.fact("hF")))
                with p.have("hh_nz: ~(HALF n = 0)").proof():
                    with p.suppose("hh_z: HALF n = 0"):
                        p.have(
                            "recon: n = COND_nat0 (ODD n) "
                            "(SUC0 (double (HALF n))) (double (HALF n))"
                        ).by(RECONSTRUCT, "n")
                        p.have("n_zero: n = 0").by_rewrite_of(
                            "recon", ["hF_eq", "hh_z", COND_F_NAT0, DOUBLE_BASE]
                        )
                        p.absurd().by_conj("hnz", "n_zero")
                p.have("hh_lt: nat0_lt (HALF n) n").by(HALF_LT_NZ, "n", "hnz")
                p.have("lb_lt: nat0_lt (low_bit (HALF n)) (HALF n)").by(
                    "IH", "HALF n", "hh_lt", "hh_nz"
                )
                p.have("ins: nat0_lt (SUC0 (low_bit (HALF n))) n").by(
                    NAT0_LT_SUC0_INSERT,
                    "low_bit (HALF n)",
                    "HALF n",
                    "n",
                    "lb_lt",
                    "hh_lt",
                )
                p.have(
                    "lb_eq: low_bit n = SUC0 (low_bit (HALF n))"
                ).by_rewrite_of("lb_n", ["hnz_eq", "hF_eq", COND_F_NAT0])
                p.thus("nat0_lt (low_bit n) n").by_rewrite_of("ins", ["lb_eq"])


# ---------------------------------------------------------------------------
# |- !n. ~(n = 0) ==> nat0_lt (clear_low n) n.
#
# Strong induction on n; case-split on ODD n.
#   ODD n  : clear_low n = double (HALF n); RECONSTRUCT (ODD n = T branch)
#            gives n = SUC0 (double (HALF n)); NAT0_LT_SUC0 closes.
#   ~ODD n : clear_low n = double (clear_low (HALF n)); RECONSTRUCT
#            (~ODD n branch) gives n = double (HALF n). HALF n != 0 (else
#            n = double 0 = 0); strong-IH at HALF n gives clear_low (HALF n)
#            < HALF n; DOUBLE_MONO_LT lifts to double (clear_low (HALF n))
#            < double (HALF n) = n.
# ---------------------------------------------------------------------------


@proof
def CLEAR_LOW_LT(p):
    from tactics import EQT_INTRO, EQF_INTRO, SYM

    p.goal("!n. ~(n = 0) ==> nat0_lt (clear_low n) n")
    with p.strong_induction("n", "IH"):
        p.assume("hnz: ~(n = 0)")
        p.have("hnz_eq: (n = 0) = F").by_thm(EQF_INTRO(p.fact("hnz")))
        p.have(
            "recon: n = COND_nat0 (ODD n) "
            "(SUC0 (double (HALF n))) (double (HALF n))"
        ).by(RECONSTRUCT, "n")
        # SPEC CLEAR_LOW_AT once at n, then rewrite-of without re-applying it
        # downstream (recursive in clear_low (HALF n) -- same loop hazard).
        p.have(
            "cl_n: clear_low n = COND_nat0 (n = 0) 0 "
            "(COND_nat0 (ODD n) (double (HALF n)) (double (clear_low (HALF n))))"
        ).by(CLEAR_LOW_AT, "n")
        with p.cases_on(EXCLUDED_MIDDLE, "ODD n"):
            with p.case("hO: ODD n"):
                p.have("hO_eq: ODD n = T").by_thm(EQT_INTRO(p.fact("hO")))
                p.have("cl_eq: clear_low n = double (HALF n)").by_rewrite_of(
                    "cl_n", ["hnz_eq", "hO_eq", COND_F_NAT0, COND_T_NAT0]
                )
                p.have("n_eq: n = SUC0 (double (HALF n))").by_rewrite_of(
                    "recon", ["hO_eq", COND_T_NAT0]
                )
                p.have(
                    "lt_succ: nat0_lt (double (HALF n)) (SUC0 (double (HALF n)))"
                ).by(NAT0_LT_SUC0, "double (HALF n)")
                # n_eq has shape ``n = SUC0 (double (HALF n))`` -- the RHS
                # mentions ``n``, so leaving it LR would loop. Flip via SYM
                # so the rule shrinks the larger term to ``n``.
                p.thus("nat0_lt (clear_low n) n").by_rewrite_of(
                    "lt_succ", ["cl_eq", SYM(p.fact("n_eq"))]
                )
            with p.case("hF: ~(ODD n)"):
                p.have("hF_eq: ODD n = F").by_thm(EQF_INTRO(p.fact("hF")))
                p.have("n_eq: n = double (HALF n)").by_rewrite_of(
                    "recon", ["hF_eq", COND_F_NAT0]
                )
                with p.have("hh_nz: ~(HALF n = 0)").proof():
                    with p.suppose("hh_z: HALF n = 0"):
                        p.have("n_zero: n = 0").by_rewrite_of(
                            "n_eq", ["hh_z", DOUBLE_BASE]
                        )
                        p.absurd().by_conj("hnz", "n_zero")
                p.have("hh_lt: nat0_lt (HALF n) n").by(HALF_LT_NZ, "n", "hnz")
                p.have("cl_lt: nat0_lt (clear_low (HALF n)) (HALF n)").by(
                    "IH", "HALF n", "hh_lt", "hh_nz"
                )
                p.have(
                    "double_lt: "
                    "nat0_lt (double (clear_low (HALF n))) (double (HALF n))"
                ).by(DOUBLE_MONO_LT, "clear_low (HALF n)", "HALF n", "cl_lt")
                p.have(
                    "cl_eq: clear_low n = double (clear_low (HALF n))"
                ).by_rewrite_of(
                    "cl_n", ["hnz_eq", "hF_eq", COND_F_NAT0]
                )
                # Same SYM(n_eq) trick as in the ODD branch.
                p.thus("nat0_lt (clear_low n) n").by_rewrite_of(
                    "double_lt", ["cl_eq", SYM(p.fact("n_eq"))]
                )


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
    print("Step 13 OK -- BIT_AT_POW2_DIFF proved.")
    print("  BIT_AT_POW2_DIFF:", pp_thm(BIT_AT_POW2_DIFF))
    print("Step 14 OK -- HALF_LT_SUC0 proved.")
    print("  HALF_LT_SUC0    :", pp_thm(HALF_LT_SUC0))
    print("Step 15 OK -- HALF_LT_NZ proved.")
    print("  HALF_LT_NZ      :", pp_thm(HALF_LT_NZ))
    print("Step 16 OK -- ZERO_BITS proved.")
    print("  ZERO_BITS       :", pp_thm(ZERO_BITS))
    print("Step 17 OK -- BIT_EXTENSIONALITY proved.")
    print("  BIT_EXTENSIONALITY:", pp_thm(BIT_EXTENSIONALITY))
    print("Step 18 OK -- set_bit defined.")
    print("  SET_BIT_BASE    :", pp_thm(SET_BIT_BASE))
    print("  SET_BIT_STEP    :", pp_thm(SET_BIT_STEP))
    print("  SET_BIT_BASE_AT :", pp_thm(SET_BIT_BASE_AT))
    print("  SET_BIT_STEP_AT :", pp_thm(SET_BIT_STEP_AT))
    print("Step 19 OK -- BIT_AT_SET_BIT_SAME proved.")
    print("  BIT_AT_SET_BIT_SAME:", pp_thm(BIT_AT_SET_BIT_SAME))
    print("Step 20 OK -- BIT_AT_SET_BIT_DIFF proved.")
    print("  BIT_AT_SET_BIT_DIFF:", pp_thm(BIT_AT_SET_BIT_DIFF))
    print("Step 21 OK -- BIT_LT proved.")
    print("  BIT_LT          :", pp_thm(BIT_LT))
    print("Step 22 OK -- low_bit / clear_low defined.")
    print("  LOW_BIT_REC     :", pp_thm(LOW_BIT_REC))
    print("  LOW_BIT_AT      :", pp_thm(LOW_BIT_AT))
    print("  CLEAR_LOW_REC   :", pp_thm(CLEAR_LOW_REC))
    print("  CLEAR_LOW_AT    :", pp_thm(CLEAR_LOW_AT))
    print("Step 23 OK -- DOUBLE_MONO_LT proved.")
    print("  DOUBLE_MONO_LT  :", pp_thm(DOUBLE_MONO_LT))
    print("Step 24 OK -- LOW_BIT_LT proved.")
    print("  LOW_BIT_LT      :", pp_thm(LOW_BIT_LT))
    print("Step 25 OK -- CLEAR_LOW_LT proved.")
    print("  CLEAR_LOW_LT    :", pp_thm(CLEAR_LOW_LT))
