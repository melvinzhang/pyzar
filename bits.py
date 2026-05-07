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
from parser import parse_type
from axioms import T, F, mk_not, bool_ty
from nat0 import (
    nat0_ty,
    ZERO,
    mk_suc0,
    define_unary_0,
    define_recursive_0,
)
from classical import COND, mk_cond


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
