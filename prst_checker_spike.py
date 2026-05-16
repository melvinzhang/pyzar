"""Spike for the PRST proof-checker PR symbol.

This file records the shape implemented by ``Proof_PRST_pr`` in ``prst_pr.py``
and validates it with a small executable reference checker.

The important design point is that modus ponens must search membership in the
tail proof list.  It must not call the single-conclusion predicate
``Proof_PRST tail f`` and ``Proof_PRST tail (Imp_pf f h)``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Iterable


# ---------------------------------------------------------------------------
# PR-symbol shape implemented in prst_pr.py.  These are formulas over symbols,
# not executable pyzar definitions.
# ---------------------------------------------------------------------------


CHECKER_SYMBOL_PLAN = """
Required helper PR symbols:

  eq_nat_pr(x, y)
      Boolean equality on nat0 codes, returning T_pt/F_pt.

  and_bool_pr(x, y), or_bool_pr(x, y)
      Boolean connectives over T_pt/F_pt.

  is_tup_pr(p)
      Returns T_pt iff p has the Tup_pt tag, i.e. tag 12.

  tup_head_pr(p), tup_tail_pr(p)
      Destructors for p = Tup_pt h t.  These are pair_left/pair_right through
      the Tup_pt payload: head = pair_left(pair_right(p)),
      tail = pair_right(pair_right(p)).

  imp_code_pr(f, h)
      Builds the code Imp_pf f h.  This is pair_ord tag 7 (pair_ord f h), or a
      wrapper around pair_ord_sym compositions.

  is_pr_axiom_pr(h)
      Decidable recogniser for is_pr_axiom h:
        is_pr_def_instance_pr(h) OR is_pr_refl_pr(h) OR
        is_logical_axiom_pr(h).


Core checker symbols:

  mem_t_pr(x, p)
      course_rec over p with y_vec = x:

        mem_t_pr(x, Empty_pt) = F_pt

        mem_t_pr(x, Tup_pt h t) =
          or_pr(eq_nat_pr(x, h), mem_t_pr(x, t))

      Course-rec implementation detail:
        the step dispatches on Pair_ord tag 12.  On tag 12, payload b is
        Pair_ord h t and rec_right is the recursive result at the payload.
        Non-Tup payload pairs forward their right-recursion result, so the
        result at the Tup node is the recursive result at t.

  exists_mp_witness_pr(h, t)
      Bounded search over members f of t:

        exists f in t. mem_t_pr(imp_code_pr(f, h), t)

      This can be implemented as a fold over t:

        exists_mp_witness_pr(h, Empty_pt) = F_pt

        exists_mp_witness_pr(h, Tup_pt f rest) =
          or_pr(
            mem_t_pr(imp_code_pr(f, h), Tup_pt f rest),
            exists_mp_witness_pr(h, rest)
          )

      The membership check is against the full earlier-list t, not just rest.
      Thread the original t through y_vec.

  valid_step_pr(h, t)
      or_pr(is_pr_axiom_pr(h), exists_mp_witness_pr(h, t))

  valid_proof_list_pr(p)
      Tup_pt-list recursion:

        valid_proof_list_pr(Empty_pt) = T_pt

        valid_proof_list_pr(Tup_pt h t) =
          and_pr(valid_proof_list_pr(t), valid_step_pr(h, t))

  Proof_PRST_pr(p, n)
      and_pr(
        is_tup_pr(p),
        and_pr(
          eq_nat_pr(tup_head_pr(p), n),
          valid_proof_list_pr(p)
        )
      )

Target theorem:

  Proof_PRST p n =
    (App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt)
"""


# ---------------------------------------------------------------------------
# Executable semantic reference model.
#
# A proof list is represented in the same orientation as Proof_PRST:
# ``Tup_pt h t`` means h is the current/final line and t contains earlier
# lines.  Python tuples below are only a lightweight stand-in for nat0 codes.
# ---------------------------------------------------------------------------


EMPTY = ("Empty_pt",)


@dataclass(frozen=True)
class Tup:
    head: object
    tail: object


@dataclass(frozen=True)
class Imp:
    antecedent: object
    consequent: object


def proof_list(lines_final_first: Iterable[object]) -> object:
    """Build a Tup_pt list from final/current line to earlier lines."""
    out: object = EMPTY
    for line in reversed(list(lines_final_first)):
        out = Tup(line, out)
    return out


def iter_tup(p: object):
    while isinstance(p, Tup):
        yield p.head
        p = p.tail
    if p != EMPTY:
        raise ValueError(f"ill-formed proof list tail: {p!r}")


def mem_t(x: object, p: object) -> bool:
    return any(line == x for line in iter_tup(p))


def exists_mp_witness(h: object, t: object) -> bool:
    return any(mem_t(Imp(f, h), t) for f in iter_tup(t))


def valid_step(h: object, t: object, is_axiom: Callable[[object], bool]) -> bool:
    return is_axiom(h) or exists_mp_witness(h, t)


def valid_proof_list(p: object, is_axiom: Callable[[object], bool]) -> bool:
    if p == EMPTY:
        return True
    if not isinstance(p, Tup):
        return False
    return valid_proof_list(p.tail, is_axiom) and valid_step(p.head, p.tail, is_axiom)


def proof_prst_checker(p: object, n: object, is_axiom: Callable[[object], bool]) -> bool:
    return isinstance(p, Tup) and p.head == n and valid_proof_list(p, is_axiom)


def old_single_head_checker(p: object, n: object, is_axiom: Callable[[object], bool]) -> bool:
    """Reference for the old broken recursive shape."""
    if not isinstance(p, Tup) or p.head != n:
        return False
    h = p.head
    t = p.tail
    return is_axiom(h) or any(
        old_single_head_checker(t, f, is_axiom)
        and old_single_head_checker(t, Imp(f, g), is_axiom)
        and h == g
        for f in iter_tup(t)
        for g in [h]
    )


def validate() -> None:
    a = "A"
    b = "B"
    c = "C"
    d = "D"
    axiom_set = {a, Imp(a, b)}
    is_axiom = axiom_set.__contains__

    axiom_only = proof_list([a])
    invalid_axiom_only = proof_list([c])
    earlier_lines = proof_list([Imp(a, b), a])
    mp_proof = Tup(b, earlier_lines)
    missing_imp = proof_list([b, a])
    missing_antecedent = proof_list([b, Imp(a, b)])
    wrong_conclusion = proof_list([c, Imp(a, b), a])
    duplicate_lines = proof_list([b, a, Imp(a, b), a])
    reversed_tail = proof_list([b, a, Imp(a, b)])
    malformed_tail = Tup(b, Tup(Imp(a, b), "not-a-tup-tail"))
    non_tup_input = "not-a-proof-list"

    # Spike 5 target: singleton axiom list.
    assert proof_prst_checker(axiom_only, a, is_axiom)
    assert not proof_prst_checker(invalid_axiom_only, c, is_axiom)
    assert not proof_prst_checker(axiom_only, b, is_axiom)

    # Spike 5 target: empty proof list is never a proof of any conclusion.
    assert not proof_prst_checker(EMPTY, a, is_axiom)
    assert not proof_prst_checker(EMPTY, b, is_axiom)
    assert not proof_prst_checker(non_tup_input, a, is_axiom)
    assert not valid_proof_list(malformed_tail, is_axiom)

    # Spike 5 target: if f and Imp_pf f g are earlier lines, adding g as the
    # new head validates by bounded membership search over the tail.
    assert proof_prst_checker(mp_proof, b, is_axiom)
    assert not proof_prst_checker(missing_imp, b, is_axiom)
    assert not proof_prst_checker(missing_antecedent, b, is_axiom)
    assert not proof_prst_checker(wrong_conclusion, c, is_axiom)
    assert not proof_prst_checker(mp_proof, c, is_axiom)
    assert proof_prst_checker(duplicate_lines, b, is_axiom)
    assert proof_prst_checker(reversed_tail, b, is_axiom)

    # A consequent with a nearby but nonmatching implication is not enough.
    assert not proof_prst_checker(proof_list([d, Imp(a, b), a]), d, is_axiom)

    # Regression guard: the valid MP proof works with membership search, but
    # failed with the old single-conclusion tail-recursion shape.
    assert not old_single_head_checker(mp_proof, b, is_axiom)


if __name__ == "__main__":
    validate()
    print("PRST checker spike validated")
