"""Spike for PRST boolean helper correctness.

The PR helpers in ``prst_pr.py`` encode booleans as:

    T_pt = Adj_pt Empty_pt Empty_pt
    F_pt = Empty_pt

and implement equality / boolean connectives with ``if_in_sym`` over
singletons. This executable reference records the intended facts that later PR
evaluation proofs should use instead of repeatedly expanding the if-in bodies.
"""

from __future__ import annotations

from dataclasses import dataclass


EMPTY = 0
F_PT = EMPTY


@dataclass(frozen=True)
class Adj:
    elem: object
    rest: object


T_PT = Adj(EMPTY, EMPTY)


def singleton(value: object) -> object:
    return Adj(value, EMPTY)


def in_pa(value: object, set_value: object) -> bool:
    if isinstance(set_value, Adj):
        return value == set_value.elem or in_pa(value, set_value.rest)
    return False


def if_in(test: object, set_value: object, then_value: object, else_value: object) -> object:
    return then_value if in_pa(test, set_value) else else_value


def eq_nat_pr(x: object, y: object) -> object:
    return if_in(x, singleton(y), T_PT, F_PT)


def or_bool_pr(x: object, y: object) -> object:
    return if_in(x, singleton(T_PT), T_PT, y)


def and_bool_pr(x: object, y: object) -> object:
    return if_in(x, singleton(T_PT), y, F_PT)


def as_bool(value: object) -> bool:
    if value == T_PT:
        return True
    if value == F_PT:
        return False
    raise ValueError(f"not a PRST boolean: {value!r}")


def validate() -> None:
    x = Adj("x", EMPTY)
    y = Adj("y", EMPTY)

    assert T_PT != F_PT

    for a in [F_PT, T_PT, x, y, 3]:
        for b in [F_PT, T_PT, x, y, 3]:
            assert eq_nat_pr(a, b) == (T_PT if a == b else F_PT)

    for a in [F_PT, T_PT]:
        for b in [F_PT, T_PT]:
            assert as_bool(or_bool_pr(a, b)) == (as_bool(a) or as_bool(b))
            assert as_bool(and_bool_pr(a, b)) == (as_bool(a) and as_bool(b))

    # The helpers intentionally branch on exactly ``x = T_pt``. They are
    # ordinary boolean connectives only under the boolean-input invariant.
    assert or_bool_pr(x, F_PT) == F_PT
    assert or_bool_pr(x, T_PT) == T_PT
    assert and_bool_pr(x, T_PT) == F_PT
    assert and_bool_pr(x, x) == F_PT

    # Useful algebraic lemmas under boolean inputs.
    for a in [F_PT, T_PT]:
        assert or_bool_pr(a, F_PT) == a
        assert or_bool_pr(a, T_PT) == T_PT
        assert and_bool_pr(a, F_PT) == F_PT
        assert and_bool_pr(a, T_PT) == a

    for a in [F_PT, T_PT]:
        for b in [F_PT, T_PT]:
            for c in [F_PT, T_PT]:
                assert or_bool_pr(a, or_bool_pr(b, c)) == or_bool_pr(or_bool_pr(a, b), c)
                assert and_bool_pr(a, and_bool_pr(b, c)) == and_bool_pr(and_bool_pr(a, b), c)
                assert and_bool_pr(a, or_bool_pr(b, c)) == or_bool_pr(
                    and_bool_pr(a, b),
                    and_bool_pr(a, c),
                )


if __name__ == "__main__":
    validate()
    print("PRST boolean helper spike validated")
