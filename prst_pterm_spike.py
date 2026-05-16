"""Spike for the PRST ``is_pterm_pr`` recognizer slice.

This is an executable reference model for the PR-level shape in ``prst_pr.py``:
``is_pterm_pr`` is not a direct syntax recursion. It is a Pair_ord course
recursion that returns an auxiliary pair

    Pair_ord(is_term_bool, child_bool_pair)

so constructor nodes can expose their own boolean while intermediate Pair_ord
payload nodes carry the child booleans needed by Tup_pt/App_pt.
"""

from __future__ import annotations

from dataclasses import dataclass


EMPTY = 0
T_PT = ("T_pt",)
F_PT = EMPTY

VAR_TAG = 2
EQ_TAG = 5
IMP_TAG = 7
APP_TAG = 11
TUP_TAG = 12

ZERO_SYM = 0
ADJ_SYM = 1
IF_IN_SYM = 3
PAIR_LEFT_SYM = 8
PAIR_RIGHT_SYM = 9
PAIR_ORD_SYM = 10


@dataclass(frozen=True)
class PairOrd:
    left: object
    right: object


@dataclass(frozen=True)
class Aux:
    is_term: object
    child_bools: object


def var_pt(v: object) -> object:
    return PairOrd(VAR_TAG, v)


def tup_pt(head: object, tail: object) -> object:
    return PairOrd(TUP_TAG, PairOrd(head, tail))


def app_pt(fn: object, args: object) -> object:
    return PairOrd(APP_TAG, PairOrd(fn, args))


def eq_pf(left: object, right: object) -> object:
    return PairOrd(EQ_TAG, PairOrd(left, right))


def imp_pf(left: object, right: object) -> object:
    return PairOrd(IMP_TAG, PairOrd(left, right))


def proj_sym(i: object, n: object) -> object:
    return PairOrd(2, PairOrd(i, n))


def rec_sym(g: object, h: object) -> object:
    return PairOrd(4, PairOrd(g, h))


def const_sym(c: object) -> object:
    return PairOrd(5, c)


def mu_sym(f: object) -> object:
    return PairOrd(6, f)


def course_rec_sym(g: object, h: object) -> object:
    return PairOrd(7, PairOrd(g, h))


def _bool_and(a: object, b: object) -> object:
    return T_PT if a == T_PT and b == T_PT else F_PT


def _is_partial_pr_sym_pr(sym: object) -> object:
    if sym in {ZERO_SYM, ADJ_SYM, IF_IN_SYM, PAIR_LEFT_SYM, PAIR_RIGHT_SYM, PAIR_ORD_SYM}:
        return T_PT
    if isinstance(sym, PairOrd) and sym.left in {2, 4, 5, 6, 7}:
        return T_PT
    return F_PT


def _is_pterm_aux(term: object) -> Aux:
    if term == EMPTY:
        return Aux(T_PT, EMPTY)
    if not isinstance(term, PairOrd):
        return Aux(F_PT, PairOrd(F_PT, F_PT))

    rec_left = _is_pterm_aux(term.left)
    rec_right = _is_pterm_aux(term.right)
    child_bools = PairOrd(rec_left.is_term, rec_right.is_term)

    if term.left == VAR_TAG:
        return Aux(T_PT, EMPTY)

    if term.left == TUP_TAG:
        payload_bools = rec_right.child_bools
        if not isinstance(payload_bools, PairOrd):
            return Aux(F_PT, EMPTY)
        return Aux(_bool_and(payload_bools.left, payload_bools.right), EMPTY)

    if term.left == APP_TAG:
        payload = term.right
        payload_bools = rec_right.child_bools
        if not isinstance(payload, PairOrd) or not isinstance(payload_bools, PairOrd):
            return Aux(F_PT, EMPTY)
        return Aux(
            _bool_and(_is_partial_pr_sym_pr(payload.left), payload_bools.right),
            EMPTY,
        )

    return Aux(F_PT, child_bools)


def is_pterm_pr(term: object) -> object:
    return _is_pterm_aux(term).is_term


def is_pr_refl_pr(formula: object) -> object:
    if not isinstance(formula, PairOrd) or formula.left != EQ_TAG:
        return F_PT
    payload = formula.right
    if not isinstance(payload, PairOrd):
        return F_PT
    return _bool_and(T_PT if payload.left == payload.right else F_PT, is_pterm_pr(payload.left))


def validate() -> None:
    x = var_pt(0)
    y = var_pt(1)
    args = tup_pt(EMPTY, tup_pt(x, EMPTY))
    app = app_pt(ADJ_SYM, args)

    assert is_pterm_pr(EMPTY) == T_PT
    assert is_pterm_pr(x) == T_PT
    assert is_pterm_pr(tup_pt(x, y)) == T_PT
    assert is_pterm_pr(app) == T_PT

    assert is_pterm_pr(app_pt(proj_sym(0, 2), tup_pt(x, y))) == T_PT
    assert is_pterm_pr(app_pt(rec_sym(ZERO_SYM, IF_IN_SYM), args)) == T_PT
    assert is_pterm_pr(app_pt(const_sym(x), tup_pt(y, EMPTY))) == T_PT
    assert is_pterm_pr(app_pt(course_rec_sym(ZERO_SYM, IF_IN_SYM), args)) == T_PT
    assert is_pterm_pr(app_pt(mu_sym(ZERO_SYM), args)) == T_PT

    assert is_pr_refl_pr(eq_pf(app, app)) == T_PT
    assert is_pr_refl_pr(eq_pf(tup_pt(x, y), tup_pt(x, y))) == T_PT

    nonterm_formula = eq_pf(x, x)
    assert is_pterm_pr(nonterm_formula) == F_PT
    assert is_pterm_pr(tup_pt(x, nonterm_formula)) == F_PT
    assert is_pterm_pr(app_pt(("not_pr_sym",), args)) == F_PT
    assert is_pterm_pr(app_pt(ADJ_SYM, nonterm_formula)) == F_PT
    assert is_pr_refl_pr(eq_pf(nonterm_formula, nonterm_formula)) == F_PT
    assert is_pr_refl_pr(imp_pf(app, app)) == F_PT


if __name__ == "__main__":
    validate()
    print("PRST is_pterm_pr spike validated")
