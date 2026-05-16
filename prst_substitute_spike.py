"""Spike for ``substitute_pr`` external correctness.

The production PR symbol in ``prst_pr.py`` implements PRST substitution by a
Pair_ord course recursion over raw encoded syntax. This reference model checks
that the course-recursive shape agrees with the direct ``substitute_p`` syntax
recursion on the constructor cases needed before proving the full theorem.
"""

from __future__ import annotations

from dataclasses import dataclass


EMPTY = 0

VAR_TAG = 2
EQ_TAG = 5
NOT_TAG = 6
IMP_TAG = 7
IN_TAG = 10
APP_TAG = 11
TUP_TAG = 12

ZERO_SYM = ("zero_sym",)
ADJ_SYM = ("adj_sym",)
IF_IN_SYM = ("if_in_sym",)


@dataclass(frozen=True)
class PairOrd:
    left: object
    right: object


def var_pt(v: object) -> object:
    return PairOrd(VAR_TAG, v)


def tup_pt(head: object, tail: object) -> object:
    return PairOrd(TUP_TAG, PairOrd(head, tail))


def app_pt(fn: object, args: object) -> object:
    return PairOrd(APP_TAG, PairOrd(fn, args))


def eq_pf(left: object, right: object) -> object:
    return PairOrd(EQ_TAG, PairOrd(left, right))


def not_pf(body: object) -> object:
    return PairOrd(NOT_TAG, body)


def imp_pf(left: object, right: object) -> object:
    return PairOrd(IMP_TAG, PairOrd(left, right))


def in_pa(left: object, right: object) -> object:
    return PairOrd(IN_TAG, PairOrd(left, right))


def pair_left(value: object) -> object:
    assert isinstance(value, PairOrd)
    return value.left


def pair_right(value: object) -> object:
    assert isinstance(value, PairOrd)
    return value.right


def substitute_direct(term: object, replacement: object, var_idx: object) -> object:
    if term == EMPTY:
        return EMPTY
    if not isinstance(term, PairOrd):
        return term

    tag = term.left
    payload = term.right

    if tag == VAR_TAG:
        return replacement if payload == var_idx else term
    if tag == TUP_TAG:
        return tup_pt(
            substitute_direct(pair_left(payload), replacement, var_idx),
            substitute_direct(pair_right(payload), replacement, var_idx),
        )
    if tag == APP_TAG:
        return app_pt(pair_left(payload), substitute_direct(pair_right(payload), replacement, var_idx))
    if tag == EQ_TAG:
        return eq_pf(
            substitute_direct(pair_left(payload), replacement, var_idx),
            substitute_direct(pair_right(payload), replacement, var_idx),
        )
    if tag == IN_TAG:
        return in_pa(
            substitute_direct(pair_left(payload), replacement, var_idx),
            substitute_direct(pair_right(payload), replacement, var_idx),
        )
    if tag == NOT_TAG:
        return not_pf(substitute_direct(payload, replacement, var_idx))
    if tag == IMP_TAG:
        return imp_pf(
            substitute_direct(pair_left(payload), replacement, var_idx),
            substitute_direct(pair_right(payload), replacement, var_idx),
        )
    return PairOrd(
        substitute_direct(tag, replacement, var_idx),
        substitute_direct(payload, replacement, var_idx),
    )


def _subst_course(term: object, y_vec: PairOrd) -> object:
    """Pair_ord course-recursive body from ``substitute_pr``.

    ``y_vec`` is ``Pair_ord replacement var_idx``.
    """
    if term == EMPTY:
        return EMPTY
    if not isinstance(term, PairOrd):
        # Nonzero nat atoms are not PRST syntax constructors in this reference.
        # The real course recursion's value here is irrelevant to well-formed
        # constructor cases except as ignored left-recursion payload.
        return EMPTY

    a = term.left
    b = term.right
    rec_left = _subst_course(a, y_vec)
    rec_right = _subst_course(b, y_vec)

    if a == VAR_TAG:
        return pair_left(y_vec) if b == pair_right(y_vec) else PairOrd(VAR_TAG, b)
    if a == EQ_TAG:
        return PairOrd(EQ_TAG, rec_right)
    if a == NOT_TAG:
        return PairOrd(NOT_TAG, rec_right)
    if a == IMP_TAG:
        return PairOrd(IMP_TAG, rec_right)
    if a == IN_TAG:
        return PairOrd(IN_TAG, rec_right)
    if a == APP_TAG:
        return PairOrd(APP_TAG, PairOrd(pair_left(b), pair_right(rec_right)))
    if a == TUP_TAG:
        return PairOrd(TUP_TAG, rec_right)
    return PairOrd(rec_left, rec_right)


def substitute_pr_ref(term: object, replacement: object, var_idx: object) -> object:
    return _subst_course(term, PairOrd(replacement, var_idx))


def _assert_subst(term: object, replacement: object, var_idx: object) -> None:
    assert substitute_pr_ref(term, replacement, var_idx) == substitute_direct(
        term,
        replacement,
        var_idx,
    )


def validate() -> None:
    x = var_pt(0)
    y = var_pt(1)
    z = var_pt(2)
    replacement = app_pt(ADJ_SYM, tup_pt(EMPTY, tup_pt(y, EMPTY)))

    _assert_subst(EMPTY, replacement, 0)
    assert substitute_pr_ref(EMPTY, replacement, 0) == EMPTY

    assert substitute_pr_ref(x, replacement, 0) == replacement
    assert substitute_pr_ref(x, replacement, 9) == x

    eq_case = eq_pf(x, tup_pt(y, EMPTY))
    assert substitute_pr_ref(eq_case, replacement, 0) == eq_pf(replacement, tup_pt(y, EMPTY))
    _assert_subst(eq_case, replacement, 0)

    in_case = in_pa(tup_pt(x, y), z)
    not_case = not_pf(in_case)
    imp_case = imp_pf(eq_case, not_case)
    _assert_subst(in_case, replacement, 0)
    _assert_subst(not_case, replacement, 0)
    _assert_subst(imp_case, replacement, 0)

    nested_tuple = tup_pt(x, tup_pt(app_pt(IF_IN_SYM, tup_pt(y, tup_pt(x, EMPTY))), EMPTY))
    _assert_subst(nested_tuple, replacement, 0)

    # App_pt keeps the function id unchanged, even when the id contains the
    # variable-shaped payload. Only the args tuple recurses.
    fn_with_var_shape = PairOrd("fn_tag", x)
    app_case = app_pt(fn_with_var_shape, tup_pt(x, tup_pt(y, EMPTY)))
    expected_app = app_pt(fn_with_var_shape, tup_pt(replacement, tup_pt(y, EMPTY)))
    assert substitute_pr_ref(app_case, replacement, 0) == expected_app
    assert substitute_direct(app_case, replacement, 0) == expected_app

    # Replacing a variable not present is identity on well-formed examples.
    for term in [x, eq_case, in_case, not_case, imp_case, nested_tuple, app_case]:
        assert substitute_pr_ref(term, replacement, 99) == term


if __name__ == "__main__":
    validate()
    print("PRST substitute_pr spike validated")
