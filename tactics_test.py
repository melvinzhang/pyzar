"""Self-tests for tactics.py — moved out of the module body (H17)."""

from fusion import Var, bool_ty, ASSUME, concl
from basics import aconv, mk_eq
from axioms import T
from tactics import SYM, EQT_INTRO, EQT_ELIM, TRUTH


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

    print("tactics.py self-tests passed.")


if __name__ == "__main__":
    main()
