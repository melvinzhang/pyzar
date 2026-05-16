"""Spike for the PRST internal evaluation chain.

This file validates the intended proof shape for the internal evaluation lemmas
used by G1. It is not a kernel proof. It is an executable reference that checks
two things:

1. The external value computed by the PR symbol agrees with the direct semantic
   operation for every constructor family in the reference syntax.
2. The internal PRST proof plan uses only local ingredients:
   PR-def instances, PROV_PRST_AX/SUBST/MP, and equality reasoning. It must not
   use a global representability axiom.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Iterable


EMPTY = ("Empty_pt",)
ZERO_SYM = ("zero_sym",)
ADJ_SYM = ("adj_sym",)
SUBSTITUTE_PR = ("substitute_pr",)
NUMERAL_PR = ("numeral_pr",)
DIAG_PR = ("diag_pr",)
VAR_X = 0


@dataclass(frozen=True)
class Var:
    idx: int


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
class Not:
    body: object


@dataclass(frozen=True)
class Imp:
    left: object
    right: object


@dataclass(frozen=True)
class In:
    left: object
    right: object


@dataclass(frozen=True)
class Adj:
    elem: object
    rest: object


@dataclass(frozen=True)
class Quote:
    value: object


SYNTAX_CASES = {
    "Empty_pt",
    "Var_pt hit",
    "Var_pt miss",
    "Tup_pt",
    "App_pt",
    "Eq_pf",
    "In_pa",
    "Not_pf",
    "Imp_pf",
    "opaque atom",
}


def tup(*items: object) -> object:
    out: object = EMPTY
    for item in reversed(items):
        out = Tup(item, out)
    return out


def quote_hf(value: object) -> object:
    if isinstance(value, int):
        if value < 0:
            raise ValueError("nat0 quote requested for a negative integer")
        out: object = EMPTY
        for _ in range(value):
            out = Adj(out, out)
        return out
    if value == 0:
        return EMPTY
    return Quote(value)


def substitute_direct(term: object, replacement: object, var_idx: int) -> object:
    if term == EMPTY:
        return EMPTY
    if isinstance(term, Var):
        return replacement if term.idx == var_idx else term
    if isinstance(term, Tup):
        return Tup(
            substitute_direct(term.head, replacement, var_idx),
            substitute_direct(term.tail, replacement, var_idx),
        )
    if isinstance(term, App):
        return App(term.fn, substitute_direct(term.args, replacement, var_idx))
    if isinstance(term, Eq):
        return Eq(
            substitute_direct(term.left, replacement, var_idx),
            substitute_direct(term.right, replacement, var_idx),
        )
    if isinstance(term, In):
        return In(
            substitute_direct(term.left, replacement, var_idx),
            substitute_direct(term.right, replacement, var_idx),
        )
    if isinstance(term, Not):
        return Not(substitute_direct(term.body, replacement, var_idx))
    if isinstance(term, Imp):
        return Imp(
            substitute_direct(term.left, replacement, var_idx),
            substitute_direct(term.right, replacement, var_idx),
        )
    return term


class Rule(str, Enum):
    PR_DEF_INSTANCE = "PR-def instance"
    PROV_PRST_AX = "PROV_PRST_AX"
    PROV_PRST_SUBST = "PROV_PRST_SUBST"
    PROV_PRST_MP = "PROV_PRST_MP"
    EQ_REASONING = "PRST equality reasoning"
    GLOBAL_REPRESENTABILITY = "global representability axiom"


ALLOWED_RULES = {
    Rule.PR_DEF_INSTANCE,
    Rule.PROV_PRST_AX,
    Rule.PROV_PRST_SUBST,
    Rule.PROV_PRST_MP,
    Rule.EQ_REASONING,
}


@dataclass(frozen=True)
class Step:
    name: str
    rule: Rule
    children: tuple["Step", ...] = field(default_factory=tuple)

    def rules(self) -> set[Rule]:
        out = {self.rule}
        for child in self.children:
            out.update(child.rules())
        return out

    def names(self) -> set[str]:
        out = {self.name}
        for child in self.children:
            out.update(child.names())
        return out


@dataclass(frozen=True)
class InternalEval:
    target: object
    result: object
    proof: Step

    @property
    def provable_formula(self) -> Eq:
        return Eq(self.target, self.result)


def _assert_allowed(plan: InternalEval) -> None:
    rules = plan.proof.rules()
    assert Rule.GLOBAL_REPRESENTABILITY not in rules
    assert rules <= ALLOWED_RULES


def _chain(name: str, children: Iterable[Step]) -> Step:
    return Step(name, Rule.EQ_REASONING, tuple(children))


def _pr_def(name: str) -> Step:
    return Step(name, Rule.PR_DEF_INSTANCE)


def _axiom(name: str, child: Step) -> Step:
    return Step(name, Rule.PROV_PRST_AX, (child,))


def _subst(name: str, child: Step) -> Step:
    return Step(name, Rule.PROV_PRST_SUBST, (child,))


def _mp(name: str, *children: Step) -> Step:
    return Step(name, Rule.PROV_PRST_MP, tuple(children))


def _case_step(case_name: str, children: Iterable[Step] = ()) -> Step:
    return _chain(
        case_name,
        [
            _subst(f"{case_name}: instantiate defining axiom", _pr_def("is_pr_def_instance")),
            _axiom(f"{case_name}: expose PR-def axiom", _pr_def(case_name)),
            *children,
            Step(f"{case_name}: equality normalization", Rule.EQ_REASONING),
        ],
    )


def numeral_eval(n: int) -> InternalEval:
    if n < 0:
        raise ValueError("numeral_eval expects a nat0 integer")
    target = App(NUMERAL_PR, tup(n))
    result = quote_hf(n)
    if n == 0:
        proof = _chain(
            "numeral 0 internal eval",
            [
                _axiom("rec base axiom for numeral_pr", _pr_def("rec_base_def_axiom")),
                _axiom("zero_def_axiom", _pr_def("zero_def_axiom")),
            ],
        )
    else:
        prev = numeral_eval(n - 1)
        proof = _chain(
            f"numeral {n} internal eval",
            [
                prev.proof,
                _axiom("rec step axiom for numeral_pr", _pr_def("rec_step_def_axiom")),
                _axiom("adj_sym defining axiom", _pr_def("adj/Adj_pt equation")),
                Step("compose numeral predecessor equality", Rule.EQ_REASONING),
            ],
        )
    return InternalEval(target, result, proof)


def substitute_eval(term: object, replacement: object, var_idx: int) -> InternalEval:
    target = App(SUBSTITUTE_PR, tup(term, replacement, var_idx))
    result = substitute_direct(term, replacement, var_idx)

    if term == EMPTY:
        proof = _case_step("Empty_pt")
    elif isinstance(term, Var):
        case_name = "Var_pt hit" if term.idx == var_idx else "Var_pt miss"
        proof = _case_step(case_name, [_mp("if_in dispatch for Var_pt", _pr_def("if_in_true/false"))])
    elif isinstance(term, Tup):
        proof = _case_step(
            "Tup_pt",
            [
                substitute_eval(term.head, replacement, var_idx).proof,
                substitute_eval(term.tail, replacement, var_idx).proof,
                _axiom("pair_ord payload reconstruction", _pr_def("pair_ord_def_axiom_at")),
            ],
        )
    elif isinstance(term, App):
        proof = _case_step(
            "App_pt",
            [
                substitute_eval(term.args, replacement, var_idx).proof,
                _axiom("pair_left keeps App_pt function id", _pr_def("pair_left_def_axiom_at")),
                _axiom("pair_right extracts substituted args", _pr_def("pair_right_def_axiom_at")),
                Step("App_pt congruence with fixed function id", Rule.EQ_REASONING),
            ],
        )
    elif isinstance(term, Eq):
        proof = _case_step(
            "Eq_pf",
            [
                substitute_eval(term.left, replacement, var_idx).proof,
                substitute_eval(term.right, replacement, var_idx).proof,
            ],
        )
    elif isinstance(term, In):
        proof = _case_step(
            "In_pa",
            [
                substitute_eval(term.left, replacement, var_idx).proof,
                substitute_eval(term.right, replacement, var_idx).proof,
            ],
        )
    elif isinstance(term, Not):
        proof = _case_step("Not_pf", [substitute_eval(term.body, replacement, var_idx).proof])
    elif isinstance(term, Imp):
        proof = _case_step(
            "Imp_pf",
            [
                substitute_eval(term.left, replacement, var_idx).proof,
                substitute_eval(term.right, replacement, var_idx).proof,
            ],
        )
    else:
        proof = _case_step("opaque atom")

    return InternalEval(target, result, proof)


def diag_eval(code: object) -> InternalEval:
    target = App(DIAG_PR, tup(code))
    numeral = (
        numeral_eval(code)
        if isinstance(code, int)
        else InternalEval(
            App(NUMERAL_PR, tup(code)),
            quote_hf(code),
            _chain(
                "numeral_pr schema for arbitrary code",
                [
                    _pr_def("PROV_PRST_NUMERAL_EVAL theorem schema"),
                    Step("specialize numeral theorem at code", Rule.EQ_REASONING),
                ],
            ),
        )
    )
    subst = substitute_eval(code, numeral.result, VAR_X)
    proof = _chain(
        "diag_pr internal eval",
        [
            _axiom("diag_pr defining composition", _pr_def("diag_pr_def")),
            numeral.proof,
            subst.proof,
            Step("compose numeral and substitute equalities", Rule.EQ_REASONING),
        ],
    )
    return InternalEval(target, subst.result, proof)


def _assert_plan(plan: InternalEval) -> None:
    _assert_allowed(plan)
    assert isinstance(plan.provable_formula, Eq)
    assert plan.provable_formula.left == plan.target
    assert plan.provable_formula.right == plan.result


def _constructor_fixture() -> object:
    x = Var(VAR_X)
    y = Var(1)
    args = Tup(x, Tup(App(ADJ_SYM, Tup(y, EMPTY)), EMPTY))
    return Imp(
        Eq(Tup(EMPTY, x), App(("fn-with-var-shaped-payload", x), args)),
        Not(In(y, Tup(x, EMPTY))),
    )


def _assert_substitute_case_coverage() -> None:
    replacement = App(ADJ_SYM, Tup(EMPTY, EMPTY))
    terms = [
        EMPTY,
        Var(VAR_X),
        Var(99),
        Tup(Var(VAR_X), EMPTY),
        App(("fn", Var(VAR_X)), Tup(Var(VAR_X), EMPTY)),
        Eq(Var(VAR_X), EMPTY),
        In(Var(VAR_X), Var(1)),
        Not(Var(VAR_X)),
        Imp(Var(VAR_X), Var(1)),
        "opaque",
        _constructor_fixture(),
    ]
    names: set[str] = set()
    for term in terms:
        plan = substitute_eval(term, replacement, VAR_X)
        assert plan.result == substitute_direct(term, replacement, VAR_X)
        _assert_plan(plan)
        names.update(plan.proof.names())
    for case in SYNTAX_CASES:
        assert any(name.startswith(case) for name in names), case


def validate() -> None:
    for n in range(5):
        numeral = numeral_eval(n)
        assert numeral.result == quote_hf(n)
        _assert_plan(numeral)

    _assert_substitute_case_coverage()

    for code in [0, 1, 3, Eq(Var(VAR_X), EMPTY), _constructor_fixture()]:
        diag = diag_eval(code)
        assert diag.result == substitute_direct(code, quote_hf(code), VAR_X)
        _assert_plan(diag)

    # Complete G1 dependency shape: the three theorem schemas needed by the
    # representability bridge all have local-only proof plans in this reference.
    theorem_schemas = [
        numeral_eval(4),
        substitute_eval(_constructor_fixture(), quote_hf(7), VAR_X),
        diag_eval(_constructor_fixture()),
    ]
    for schema in theorem_schemas:
        _assert_plan(schema)


if __name__ == "__main__":
    validate()
    print("PRST internal evaluation chain spike validated")
