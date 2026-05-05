#!/usr/bin/env python3
"""Linter: identify lines inside ``@proof`` bodies that bypass the declarative DSL.

A proof is *declarative* if it uses only the ``proof.py`` API exposed on the
``p: Proof`` object (``goal``/``fix``/``assume``/``have``/``thus``/``by``/
``by_rewrite``/``by_match``/``cases_on``/``induction``/``calc``/``simp``/...) plus
term constructors (``mk_eq``, ``mk_app``, ...) and destructors (``dest_*``,
``is_*``, ``rator``, ``rand``, ``aconv``, ``type_of``, ...).

Direct calls to kernel inference rules (``REFL``, ``TRANS``, ``MK_COMB``, ``ABS``,
``EQ_MP``, ``ASSUME``, ``INST``, ...) and derived tactics (``SPEC``, ``GEN``,
``MP``, ``DISCH``, ``CONJ``, ``DISJ_CASES``, ``REWRITE_RULE``, ``REWRITE_PROVE``,
``CHOOSE_WITNESS``, ``EXISTS``, ...) bypass the DSL and are flagged.

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


# Kernel inference rules and derived tactics. Calls to any of these from inside
# an ``@proof`` body are non-declarative.
NON_DECLARATIVE_NAMES = frozenset(
    {
        # fusion.py -- primitive inference rules
        "REFL",
        "TRANS",
        "MK_COMB",
        "ABS",
        "BETA",
        "ASSUME",
        "EQ_MP",
        "DEDUCT_ANTISYM_RULE",
        "INST",
        "INST_TYPE",
        "new_axiom",
        "new_basic_definition",
        "new_basic_type_definition",
        # tactics.py -- derived rules
        "AP_TERM",
        "AP_THM",
        "BETA_CONV",
        "BETA_NORM",
        "BETA_RULE",
        "beta_after",
        "SYM",
        "EQT_ELIM",
        "EQT_INTRO",
        "SPEC",
        "SPECL",
        "GEN",
        "GENL",
        "CONJ",
        "CONJUNCT1",
        "CONJUNCT2",
        "DISCH",
        "DISCHL",
        "MP",
        "UNDISCH",
        "MP_LIST",
        "CONTR",
        "NOT_ELIM",
        "NOT_INTRO",
        "EQF_INTRO",
        "EQF_ELIM",
        "DISJ1",
        "DISJ2",
        "DISJ_CASES",
        "CASE_OR",
        "MK_EQ",
        "NE_SYM",
        "REWRITE_NE",
        "subst_term",
        "EXISTS",
        "EXISTS_AT",
        "TRANS_CHAIN",
        "PROVE_HYP",
        "CHOOSE_WITNESS",
        "ELIM_EX",
        "FUN_EXT",
        "UNFOLD",
        "unfold_def_at",
        "REWRITE_CONV",
        "REWRITE_RULE",
        "REWRITE_PROVE",
        "AC_NORM",
        "AC_PROVE",
    }
)


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


def find_offenders(path):
    """Return list of ``(lineno, col, name, line_text, fn_name)`` tuples."""
    src = pathlib.Path(path).read_text()
    tree = ast.parse(src, filename=str(path))
    lines = src.splitlines()
    out = []
    for fn in _proof_functions(tree):
        for sub in ast.walk(fn):
            if not isinstance(sub, ast.Call):
                continue
            name = _callable_name(sub.func)
            if name in NON_DECLARATIVE_NAMES:
                line_text = (
                    lines[sub.lineno - 1] if 0 <= sub.lineno - 1 < len(lines) else ""
                )
                out.append(
                    (sub.lineno, sub.col_offset + 1, name, line_text.strip(), fn.name)
                )
    return out


def main(argv):
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    grand_total = 0
    by_file = []
    for raw in argv[1:]:
        path = pathlib.Path(raw)
        if not path.is_file():
            print(f"lint_declarative: not a file: {raw}", file=sys.stderr)
            return 2
        offenders = find_offenders(path)
        by_file.append((path, offenders))
        grand_total += len(offenders)
        for ln, col, name, text, fn in offenders:
            print(f"{path}:{ln}:{col}: [{fn}] {name} -- {text}")
    if len(by_file) > 1:
        print(file=sys.stderr)
        for path, offenders in by_file:
            print(f"  {path}: {len(offenders)}", file=sys.stderr)
    print(
        f"\n{grand_total} non-declarative call(s) in {len(by_file)} file(s)",
        file=sys.stderr,
    )
    return 1 if grand_total else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
