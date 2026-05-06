#!/usr/bin/env python3
"""Linter: identify lines inside ``@proof`` bodies that bypass the declarative DSL.

A proof is *declarative* if it uses only the ``proof.py`` API exposed on the
``p: Proof`` object (``goal``/``fix``/``assume``/``have``/``thus``/``by``/
``by_rewrite``/``by_match``/``cases_on``/``induction``/``calc``/``simp``/...) plus
term constructors (``mk_eq``, ``mk_app``, ...) and destructors (``dest_*``,
``is_*``, ``rator``, ``rand``, ``aconv``, ``type_of``, ...).

Two kinds of non-declarative pattern are flagged:

* ``ESCAPE`` -- a direct call to a kernel inference rule (``REFL``, ``TRANS``,
  ``MK_COMB``, ``EQ_MP``, ``INST``, ...) or derived tactic (``SPEC``, ``MP``,
  ``CONJ``, ``DISJ_CASES``, ``REWRITE_RULE``, ``CHOOSE_WITNESS``, ...) inside
  a ``@proof`` body. Each escape is one kernel leak that the DSL doesn't yet
  cover.

* ``PROCEDURAL`` -- an assignment ``name = ...`` whose RHS constructs a
  theorem (via a kernel rule, derived tactic, or a thm-producing
  ``Proof`` method like ``p.cong`` / ``p.sym`` / ``p.ne_sym`` / ``p.spec``).
  Such bindings introduce a *named theorem* into the surrounding scope
  without ever stating its conclusion as a parsed term -- the reader has
  to mentally evaluate the RHS to know what ``name`` proves. The
  declarative form is ``p.have("name: <conclusion>").by_*(...)``.

When a procedural assignment's RHS already contains an escape, only the
procedural line is reported (the inner escape is considered covered by
fixing the binding pattern).

Term-building helpers (``mk_eq``, ``mk_app``, ``mk_abs``, ``mk_comb``,
``mk_const``, ``mk_var``, ``mk_forall``, ``mk_exists``, ``mk_select``,
``mk_imp``, ``mk_or``, ``mk_and``, ``mk_not``, ``mk_fun_ty``, ``mk_type``)
and destructors (``dest_*``, ``is_*``, ``rator``, ``rand``, ``aconv``,
``type_of``, ``frees``, ``vfree_in``, ...) are *not* flagged: every proof
needs to write terms.

Usage:
    uv run python lint_declarative.py FILE [FILE ...]

Exit code 0 if every scanned ``@proof`` body is declarative, 1 otherwise.
"""

import ast
import pathlib
import sys

import fusion
import tactics


# fusion.py mixes inference rules with term/type helpers; the rules are the
# ALL_CAPS callables plus this lowercase trio. tactics.py is entirely derived
# rules, so every top-level callable defined there counts.
_FUSION_LOWERCASE_RULES = frozenset(
    {"new_axiom", "new_basic_definition", "new_basic_type_definition"}
)


def _module_callables(mod):
    return {
        name
        for name, val in vars(mod).items()
        if not name.startswith("_")
        and callable(val)
        and getattr(val, "__module__", None) == mod.__name__
    }


def _collect_non_declarative_names():
    fusion_names = _module_callables(fusion)
    rules = {n for n in fusion_names if n.isupper() or n in _FUSION_LOWERCASE_RULES}
    rules |= _module_callables(tactics)
    # Sentinel check: a refactor that breaks introspection (e.g. moves rules to
    # a new module) would otherwise silently produce an empty allowlist.
    for sentinel in ("REFL", "TRANS", "SPEC", "SYM", "MP"):
        assert sentinel in rules, f"lint introspection lost sentinel {sentinel}"
    return frozenset(rules)


# Kernel inference rules and derived tactics. Calls to any of these from inside
# an ``@proof`` body are non-declarative.
NON_DECLARATIVE_NAMES = _collect_non_declarative_names()


# DSL methods on the ``Proof`` object that *construct* (rather than just look
# up) a theorem. Used to detect procedural binding patterns where the
# constructed theorem is captured into a Python local for kernel-style
# chaining instead of being asserted via a ``have``/``thus`` claim.
# ``fact`` and ``unfold`` are deliberately excluded: ``fact`` is a lookup,
# ``unfold`` primarily side-effects (registers a fact in the frame).
PROC_DSL_METHODS = frozenset({"cong", "sym", "ne_sym", "spec"})


def _is_proof_decorator(dec):
    """``@proof`` or ``@contra_finder`` (which stacks atop ``@proof``)."""
    if isinstance(dec, ast.Call):
        return _is_proof_decorator(dec.func)
    if isinstance(dec, ast.Name):
        return dec.id in {"proof", "contra_finder"}
    if isinstance(dec, ast.Attribute):
        return dec.attr in {"proof", "contra_finder"}
    return False


def _callable_name(node):
    """Leaf name of a call's ``func``: ``Name`` -> id, ``Attribute`` -> attr."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return None


def _proof_functions(tree):
    """Yield every ``FunctionDef`` decorated with ``@proof``/``@contra_finder``."""
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if any(_is_proof_decorator(d) for d in node.decorator_list):
                yield node


def _proc_thm_call(rhs):
    """Return the first thm-producing ``Call`` within ``rhs``, or ``None``.

    A call is thm-producing if its callee leaf name is a kernel/tactic rule
    (``NON_DECLARATIVE_NAMES``) or a recognized DSL thm-constructor method
    (``PROC_DSL_METHODS``). The call may appear at any depth of the RHS,
    so e.g. ``TRANS(p.cong(...), p.spec(...))`` matches the outer ``TRANS``.
    """
    for sub in ast.walk(rhs):
        if not isinstance(sub, ast.Call):
            continue
        name = _callable_name(sub.func)
        if name in NON_DECLARATIVE_NAMES or name in PROC_DSL_METHODS:
            return sub
    return None


def _assigned_value(stmt):
    """RHS of an Assign / AnnAssign / AugAssign, or ``None`` if no value."""
    if isinstance(stmt, (ast.Assign, ast.AugAssign)):
        return stmt.value
    if isinstance(stmt, ast.AnnAssign):
        return stmt.value  # may be None for bare annotations
    return None


def find_offenders(path):
    """Return list of ``(lineno, col, name, line_text, fn_name, kind)`` tuples.

    ``kind`` is ``"ESCAPE"`` (kernel rule called inside ``@proof``) or
    ``"PROCEDURAL"`` (assignment binds a constructed theorem to a Python
    local instead of stating it via ``have``/``thus``). Escapes that fall
    inside a procedural assignment's RHS are suppressed.
    """
    src = pathlib.Path(path).read_text()
    tree = ast.parse(src, filename=str(path))
    lines = src.splitlines()
    out = []
    for fn in _proof_functions(tree):
        # Pass 1: procedural assignments. Track Call nodes inside each
        # procedural RHS so the escape pass can suppress them.
        covered = set()
        for sub in ast.walk(fn):
            rhs = _assigned_value(sub) if isinstance(
                sub, (ast.Assign, ast.AnnAssign, ast.AugAssign)
            ) else None
            if rhs is None:
                continue
            call = _proc_thm_call(rhs)
            if call is None:
                continue
            line_text = (
                lines[sub.lineno - 1] if 0 <= sub.lineno - 1 < len(lines) else ""
            )
            out.append(
                (
                    sub.lineno,
                    sub.col_offset + 1,
                    _callable_name(call.func),
                    line_text.strip(),
                    fn.name,
                    "PROCEDURAL",
                )
            )
            for c in ast.walk(rhs):
                if isinstance(c, ast.Call):
                    covered.add(id(c))
        # Pass 2: bare escapes (calls to kernel rules outside a procedural RHS).
        for sub in ast.walk(fn):
            if not isinstance(sub, ast.Call) or id(sub) in covered:
                continue
            name = _callable_name(sub.func)
            if name in NON_DECLARATIVE_NAMES:
                line_text = (
                    lines[sub.lineno - 1] if 0 <= sub.lineno - 1 < len(lines) else ""
                )
                out.append(
                    (
                        sub.lineno,
                        sub.col_offset + 1,
                        name,
                        line_text.strip(),
                        fn.name,
                        "ESCAPE",
                    )
                )
    out.sort(key=lambda r: (r[0], r[1]))
    return out


def main(argv):
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    total_escape = 0
    total_proc = 0
    by_file = []
    for raw in argv[1:]:
        path = pathlib.Path(raw)
        if not path.is_file():
            print(f"lint_declarative: not a file: {raw}", file=sys.stderr)
            return 2
        offenders = find_offenders(path)
        n_esc = sum(1 for r in offenders if r[5] == "ESCAPE")
        n_proc = sum(1 for r in offenders if r[5] == "PROCEDURAL")
        by_file.append((path, n_esc, n_proc))
        total_escape += n_esc
        total_proc += n_proc
        for ln, col, name, text, fn, kind in offenders:
            tag = name if kind == "ESCAPE" else f"PROC:{name}"
            print(f"{path}:{ln}:{col}: [{fn}] {tag} -- {text}")
    if len(by_file) > 1:
        print(file=sys.stderr)
        for path, n_esc, n_proc in by_file:
            print(f"  {path}: {n_esc} escape, {n_proc} procedural", file=sys.stderr)
    grand_total = total_escape + total_proc
    print(
        f"\n{total_escape} escape(s) + {total_proc} procedural line(s) "
        f"= {grand_total} non-declarative occurrence(s) in {len(by_file)} file(s)",
        file=sys.stderr,
    )
    return 1 if grand_total else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
