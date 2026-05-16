r"""Spike for PRST PR-def-instance recognition.

The open question is whether ``is_pr_def_instance_pr`` should use a generic
bounded witness search for

    exists F t v. is_pr_def F /\ n = substitute_p F t v

or a schema-specific matcher.

This spike validates the matcher route on every current ``is_pr_def`` family.
It deliberately avoids relying on a numeric bound for ``F``: substitution can
shrink ``Var_pt`` leaves, so a naive ``F < n`` search is not a stable
invariant.
"""

from __future__ import annotations

from dataclasses import dataclass, fields, is_dataclass


EMPTY = ("Empty_pt",)
ZERO_SYM = ("zero_sym",)
ADJ_SYM = ("adj_sym",)
IF_IN_SYM = ("if_in_sym",)
PAIR_LEFT_SYM = ("pair_left_sym",)
PAIR_RIGHT_SYM = ("pair_right_sym",)
PAIR_ORD_SYM = ("pair_ord_sym",)


@dataclass(frozen=True)
class Var:
    idx: int


@dataclass(frozen=True)
class ProjSym:
    idx: int
    arity: int


@dataclass(frozen=True)
class RecSym:
    g: object
    h: object


@dataclass(frozen=True)
class ConstSym:
    value: object


@dataclass(frozen=True)
class CourseRecSym:
    g: object
    h: object


@dataclass(frozen=True)
class PairOrd:
    left: object
    right: object


@dataclass(frozen=True)
class Tup:
    head: object
    tail: object


@dataclass(frozen=True)
class App:
    fn: object
    args: object


@dataclass(frozen=True)
class Eq:
    left: object
    right: object


@dataclass(frozen=True)
class Imp:
    left: object
    right: object


@dataclass(frozen=True)
class In:
    left: object
    right: object


@dataclass(frozen=True)
class Not:
    body: object


def tup(*items: object) -> object:
    out: object = EMPTY
    for item in reversed(items):
        out = Tup(item, out)
    return out


def substitute(term: object, replacement: object, var_idx: int) -> object:
    if term == EMPTY:
        return EMPTY
    if isinstance(term, Var):
        return replacement if term.idx == var_idx else term
    if isinstance(term, PairOrd):
        return PairOrd(
            substitute(term.left, replacement, var_idx),
            substitute(term.right, replacement, var_idx),
        )
    if isinstance(term, Tup):
        return Tup(
            substitute(term.head, replacement, var_idx),
            substitute(term.tail, replacement, var_idx),
        )
    if isinstance(term, App):
        # PRST substitution recurses into the argument tuple, not the function id.
        return App(term.fn, substitute(term.args, replacement, var_idx))
    if isinstance(term, Eq):
        return Eq(
            substitute(term.left, replacement, var_idx),
            substitute(term.right, replacement, var_idx),
        )
    if isinstance(term, In):
        return In(
            substitute(term.left, replacement, var_idx),
            substitute(term.right, replacement, var_idx),
        )
    if isinstance(term, Not):
        return Not(substitute(term.body, replacement, var_idx))
    if isinstance(term, Imp):
        return Imp(
            substitute(term.left, replacement, var_idx),
            substitute(term.right, replacement, var_idx),
        )
    return term


def _tuple_to_list(term: object) -> list[object] | None:
    out: list[object] = []
    while isinstance(term, Tup):
        out.append(term.head)
        term = term.tail
    if term != EMPTY:
        return None
    return out


def _unify_subst(template: object, candidate: object, var_idx: int) -> object | None:
    """Return the replacement term if candidate is template[var_idx := t]."""
    unset = object()
    failed = object()

    def go(left: object, right: object, replacement: object) -> object:
        if isinstance(left, Var):
            if left.idx != var_idx:
                return replacement if left == right else failed
            if replacement is unset:
                return right
            return replacement if replacement == right else failed

        if left == EMPTY or not is_dataclass(left):
            return replacement if left == right else failed
        if type(left) is not type(right):
            return failed
        if isinstance(left, (ProjSym, RecSym, ConstSym, CourseRecSym)):
            # Function-symbol payloads are not substituted under App_pt.
            return replacement if left == right else failed

        out = replacement
        for field in fields(left):
            out = go(getattr(left, field.name), getattr(right, field.name), out)
            if out is failed:
                return failed
        return out

    found = go(template, candidate, unset)
    return None if found is failed or found is unset else found


def _free_var_indices(term: object) -> set[int]:
    if isinstance(term, Var):
        return {term.idx}
    if term == EMPTY or not is_dataclass(term):
        return set()
    if isinstance(term, (ProjSym, RecSym, ConstSym, CourseRecSym)):
        return set()
    out: set[int] = set()
    for field in fields(term):
        out.update(_free_var_indices(getattr(term, field.name)))
    return out


def _is_subst_instance(template: object, candidate: object) -> bool:
    if candidate == template:
        return True
    return any(
        _unify_subst(template, candidate, var_idx) is not None
        for var_idx in _free_var_indices(template)
    )


def var_t_args_rev(arity: int) -> object:
    out: object = EMPTY
    for idx in range(arity):
        out = Tup(Var(idx), out)
    return out


def _app(fn: object, *args: object) -> App:
    return App(fn, tup(*args))


def _adj(a: object, b: object) -> App:
    return _app(ADJ_SYM, a, b)


def _course_rec_app(g: object, h: object, arg: object, y: object) -> App:
    return _app(CourseRecSym(g, h), arg, y)


def zero_def_axiom() -> Eq:
    return Eq(App(ZERO_SYM, EMPTY), EMPTY)


def proj_def_axiom(idx: int, arity: int) -> Eq:
    return Eq(App(ProjSym(idx, arity), var_t_args_rev(arity)), Var(idx))


def if_in_true_def_axiom() -> Imp:
    return Imp(
        In(Var(0), Var(1)),
        Eq(_app(IF_IN_SYM, Var(0), Var(1), Var(2), Var(3)), Var(2)),
    )


def if_in_false_def_axiom() -> Imp:
    return Imp(
        Not(In(Var(0), Var(1))),
        Eq(_app(IF_IN_SYM, Var(0), Var(1), Var(2), Var(3)), Var(3)),
    )


def rec_base_def_axiom(g: object, h: object) -> Eq:
    return Eq(_app(RecSym(g, h), EMPTY, Var(0)), _app(g, Var(0)))


def rec_step_def_axiom(g: object, h: object) -> Eq:
    return Eq(
        _app(RecSym(g, h), _adj(Var(1), Var(2)), Var(0)),
        _app(h, Var(1), Var(2), _app(RecSym(g, h), Var(2), Var(0)), Var(0)),
    )


def const_def_axiom(value: object) -> Eq:
    return Eq(_app(ConstSym(value), Var(0)), value)


def course_rec_base_def_axiom(g: object, h: object) -> Eq:
    return Eq(_course_rec_app(g, h, EMPTY, Var(0)), _app(g, Var(0)))


def course_rec_step_def_axiom(g: object, h: object, a: object, b: object) -> Eq:
    return Eq(
        _course_rec_app(g, h, PairOrd(a, b), Var(0)),
        _app(
            h,
            a,
            b,
            _course_rec_app(g, h, a, Var(0)),
            _course_rec_app(g, h, b, Var(0)),
            Var(0),
        ),
    )


def pair_left_def_axiom(a: object, b: object) -> Eq:
    return Eq(_app(PAIR_LEFT_SYM, PairOrd(a, b)), a)


def pair_right_def_axiom(a: object, b: object) -> Eq:
    return Eq(_app(PAIR_RIGHT_SYM, PairOrd(a, b)), b)


def pair_ord_def_axiom(a: object, b: object) -> Eq:
    return Eq(_app(PAIR_ORD_SYM, a, b), PairOrd(a, b))


def _is_pr_sym(sym: object) -> bool:
    if sym in {ZERO_SYM, ADJ_SYM, IF_IN_SYM, PAIR_LEFT_SYM, PAIR_RIGHT_SYM, PAIR_ORD_SYM}:
        return True
    if isinstance(sym, ProjSym):
        return 0 <= sym.idx < sym.arity
    if isinstance(sym, RecSym):
        return _is_pr_sym(sym.g) and _is_pr_sym(sym.h)
    if isinstance(sym, ConstSym):
        return True
    if isinstance(sym, CourseRecSym):
        return _is_pr_sym(sym.g) and _is_pr_sym(sym.h)
    return False


def _match_zero(term: object) -> bool:
    return _is_subst_instance(zero_def_axiom(), term)


def _match_proj(term: object) -> bool:
    if not isinstance(term, Eq) or not isinstance(term.left, App):
        return False
    if not isinstance(term.left.fn, ProjSym):
        return False
    sym = term.left.fn
    if not 0 <= sym.idx < sym.arity:
        return False
    return _is_subst_instance(proj_def_axiom(sym.idx, sym.arity), term)


def _match_if_in_true(term: object) -> bool:
    return _is_subst_instance(if_in_true_def_axiom(), term)


def _match_if_in_false(term: object) -> bool:
    return _is_subst_instance(if_in_false_def_axiom(), term)


def _match_rec_base(term: object) -> bool:
    if not isinstance(term, Eq) or not isinstance(term.left, App):
        return False
    if not isinstance(term.left.fn, RecSym):
        return False
    sym = term.left.fn
    if not (_is_pr_sym(sym.g) and _is_pr_sym(sym.h)):
        return False
    return _is_subst_instance(rec_base_def_axiom(sym.g, sym.h), term)


def _match_rec_step(term: object) -> bool:
    if not isinstance(term, Eq) or not isinstance(term.left, App):
        return False
    if not isinstance(term.left.fn, RecSym):
        return False
    sym = term.left.fn
    if not (_is_pr_sym(sym.g) and _is_pr_sym(sym.h)):
        return False
    return _is_subst_instance(rec_step_def_axiom(sym.g, sym.h), term)


def _match_const(term: object) -> bool:
    if not isinstance(term, Eq) or not isinstance(term.left, App):
        return False
    if not isinstance(term.left.fn, ConstSym):
        return False
    return _is_subst_instance(const_def_axiom(term.left.fn.value), term)


def _match_course_rec_base(term: object) -> bool:
    if not isinstance(term, Eq) or not isinstance(term.left, App):
        return False
    if not isinstance(term.left.fn, CourseRecSym):
        return False
    sym = term.left.fn
    if not (_is_pr_sym(sym.g) and _is_pr_sym(sym.h)):
        return False
    return _is_subst_instance(course_rec_base_def_axiom(sym.g, sym.h), term)


def _match_course_rec_step(term: object) -> bool:
    if not isinstance(term, Eq) or not isinstance(term.left, App):
        return False
    if not isinstance(term.left.fn, CourseRecSym):
        return False
    sym = term.left.fn
    if not (_is_pr_sym(sym.g) and _is_pr_sym(sym.h)):
        return False
    args = _tuple_to_list(term.left.args)
    if args is None or len(args) != 2 or not isinstance(args[0], PairOrd):
        return False
    return _is_subst_instance(
        course_rec_step_def_axiom(sym.g, sym.h, args[0].left, args[0].right),
        term,
    )


def _match_pair_left(term: object) -> bool:
    if not isinstance(term, Eq) or not isinstance(term.left, App):
        return False
    if term.left.fn != PAIR_LEFT_SYM:
        return False
    args = _tuple_to_list(term.left.args)
    if args is None or len(args) != 1 or not isinstance(args[0], PairOrd):
        return False
    return _is_subst_instance(pair_left_def_axiom(args[0].left, args[0].right), term)


def _match_pair_right(term: object) -> bool:
    if not isinstance(term, Eq) or not isinstance(term.left, App):
        return False
    if term.left.fn != PAIR_RIGHT_SYM:
        return False
    args = _tuple_to_list(term.left.args)
    if args is None or len(args) != 1 or not isinstance(args[0], PairOrd):
        return False
    return _is_subst_instance(pair_right_def_axiom(args[0].left, args[0].right), term)


def _match_pair_ord(term: object) -> bool:
    if not isinstance(term, Eq) or not isinstance(term.left, App):
        return False
    if term.left.fn != PAIR_ORD_SYM:
        return False
    args = _tuple_to_list(term.left.args)
    if args is None or len(args) != 2:
        return False
    return _is_subst_instance(pair_ord_def_axiom(args[0], args[1]), term)


MATCHERS = [
    _match_zero,
    _match_proj,
    _match_if_in_true,
    _match_if_in_false,
    _match_rec_base,
    _match_rec_step,
    _match_const,
    _match_course_rec_base,
    _match_course_rec_step,
    _match_pair_left,
    _match_pair_right,
    _match_pair_ord,
]


def is_pr_def_instance_matcher(term: object) -> bool:
    return any(matcher(term) for matcher in MATCHERS)


def _assert_matches_all_subst(template: object, max_var: int, replacement: object) -> None:
    assert is_pr_def_instance_matcher(template)
    for var_idx in range(max_var + 1):
        assert is_pr_def_instance_matcher(substitute(template, replacement, var_idx))


def validate() -> None:
    x = _app(ConstSym(EMPTY), EMPTY)
    g = ZERO_SYM
    h = IF_IN_SYM
    a = Var(1)
    b = _app(ADJ_SYM, Var(2), EMPTY)
    c = PairOrd(Var(0), Var(2))

    _assert_matches_all_subst(zero_def_axiom(), 2, x)
    _assert_matches_all_subst(proj_def_axiom(1, 3), 4, x)
    _assert_matches_all_subst(if_in_true_def_axiom(), 4, x)
    _assert_matches_all_subst(if_in_false_def_axiom(), 4, x)
    _assert_matches_all_subst(rec_base_def_axiom(g, h), 2, x)
    _assert_matches_all_subst(rec_step_def_axiom(g, h), 3, x)
    _assert_matches_all_subst(const_def_axiom(c), 3, x)
    _assert_matches_all_subst(course_rec_base_def_axiom(g, h), 2, x)
    _assert_matches_all_subst(course_rec_step_def_axiom(g, h, a, b), 3, x)
    _assert_matches_all_subst(pair_left_def_axiom(a, b), 3, x)
    _assert_matches_all_subst(pair_right_def_axiom(a, b), 3, x)
    _assert_matches_all_subst(pair_ord_def_axiom(a, b), 3, x)

    malformed_if = Imp(
        In(x, Var(1)),
        Eq(_app(IF_IN_SYM, Var(0), Var(1), Var(2), Var(3)), Var(2)),
    )
    assert not is_pr_def_instance_matcher(malformed_if)

    malformed_proj = Eq(App(ProjSym(1, 3), tup(Var(2), x, Var(0))), Var(1))
    assert not is_pr_def_instance_matcher(malformed_proj)

    bad_guard_proj = Eq(App(ProjSym(3, 3), var_t_args_rev(3)), Var(3))
    assert not is_pr_def_instance_matcher(bad_guard_proj)

    bad_rec_guard = rec_base_def_axiom(("not_pr_sym",), h)
    assert not is_pr_def_instance_matcher(bad_rec_guard)

    malformed_rec_step = rec_step_def_axiom(g, h)
    assert isinstance(malformed_rec_step, Eq)
    malformed_rec_step = Eq(malformed_rec_step.left, _app(h, Var(1), Var(2), x, Var(0)))
    assert not is_pr_def_instance_matcher(malformed_rec_step)

    malformed_const = Eq(_app(ConstSym(c), x), Var(1))
    assert not is_pr_def_instance_matcher(malformed_const)

    malformed_course = course_rec_step_def_axiom(g, h, a, b)
    assert isinstance(malformed_course, Eq)
    malformed_course = Eq(malformed_course.left, _app(h, a, b, x, x, Var(0)))
    assert not is_pr_def_instance_matcher(malformed_course)

    assert not is_pr_def_instance_matcher(Eq(x, Var(2)))


if __name__ == "__main__":
    validate()
    print("PRST def-instance matcher spike validated")
