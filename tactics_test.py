"""Self-tests for tactics.py — moved out of the module body (H17)."""

from fusion import Var, bool_ty, ASSUME, concl, HolError
from basics import aconv, mk_eq, mk_app, mk_fun_ty
from axioms import T, F, mk_or
from tactics import (
    SYM,
    EQT_INTRO,
    EQT_ELIM,
    TRUTH,
    REWRITE_CONV,
    OR_CONG,
    OR_F_LEFT,
    OR_F_RIGHT,
    or_chain_collapse,
)


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

    # OR_CONG : a = c, b = d  ==>  (a \/ b) = (c \/ d)
    a, b, c, d = (Var(n, bool_ty) for n in "abcd")
    th_ac = ASSUME(mk_eq(a, c))
    th_bd = ASSUME(mk_eq(b, d))
    th_or = OR_CONG(th_ac, th_bd)
    assert aconv(concl(th_or), mk_eq(mk_or(a, b), mk_or(c, d)))
    assert set(th_or._asl) == {mk_eq(a, c), mk_eq(b, d)}

    # OR_F_LEFT / OR_F_RIGHT shape.
    pv = Var("p", bool_ty)
    assert aconv(concl(OR_F_LEFT), concl(OR_F_LEFT))  # trivially holds
    # (Better: just check pp.)
    from parser import pp_thm

    assert pp_thm(OR_F_LEFT) == "|- (!p. ((F \\/ p) = p))"
    assert pp_thm(OR_F_RIGHT) == "|- (!p. ((p \\/ F) = p))"

    # or_chain_collapse: 4-disjunct body, only middle survives.
    d1, d2, d3, d4 = (Var(n, bool_ty) for n in ("d1", "d2", "d3", "d4"))
    e2 = Var("e2", bool_ty)
    eq1 = ASSUME(mk_eq(d1, F))  # |- d1 = F
    eq2 = ASSUME(mk_eq(d2, e2))  # |- d2 = e2
    eq3 = ASSUME(mk_eq(d3, F))  # |- d3 = F
    eq4 = ASSUME(mk_eq(d4, F))  # |- d4 = F
    out = or_chain_collapse([eq1, eq2, eq3, eq4])
    expected_lhs = mk_or(d1, mk_or(d2, mk_or(d3, d4)))
    # After OR_F_LEFT/RIGHT: F \/ e2 \/ F \/ F → e2.
    assert aconv(concl(out), mk_eq(expected_lhs, e2)), (
        f"or_chain_collapse: got {pp_thm(out)}"
    )

    # All-F: collapses to F.
    eq2_F = ASSUME(mk_eq(d2, F))
    out_all_F = or_chain_collapse([eq1, eq2_F, eq3, eq4])
    assert aconv(concl(out_all_F), mk_eq(expected_lhs, F)), (
        f"or_chain_collapse all-F: got {pp_thm(out_all_F)}"
    )

    # Empty list raises.
    try:
        or_chain_collapse([])
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError on empty list")

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
