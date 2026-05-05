"""Self-tests for tactics.py — moved out of the module body (H17)."""

from fusion import Var, bool_ty, ASSUME, concl, HolError
from basics import aconv, mk_eq, mk_app, mk_fun_ty
from axioms import T
from tactics import SYM, EQT_INTRO, EQT_ELIM, TRUTH, REWRITE_CONV


def main():
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

    # REWRITE_CONV blow-up guard: a self-recursive rule whose RHS contains
    # two copies of the LHS doubles term size per pass. The fail-fast guard
    # should trigger after SIMP_GROWTH_PASSES (3) consecutive >2x passes,
    # rather than running until SIMP_OUTER_PASS_LIMIT and consuming
    # exponential time/memory.
    x = Var("x", bool_ty)
    f = Var("f", mk_fun_ty(bool_ty, mk_fun_ty(bool_ty, bool_ty)))
    fxx = mk_app(f, x, x)
    bad_rule = ASSUME(mk_eq(x, fxx))  # x = f x x — empty foralls, fires literally
    try:
        REWRITE_CONV([bad_rule], x)
    except HolError as e:
        msg = str(e)
        assert "consecutive passes" in msg, (
            f"expected blow-up guard message, got: {msg}"
        )
    else:
        raise AssertionError("expected REWRITE_CONV to abort on self-recursive rule")

    print("tactics.py self-tests passed.")


if __name__ == "__main__":
    main()
