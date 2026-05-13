#!/usr/bin/env python3
"""Emit a Graphviz DOT graph of proof dependencies in a Python module.

A *node* is a top-level ``FunctionDef`` whose decorator list contains
``@proof``. Wrappers like ``@contra_finder`` stack on top of ``@proof``,
so they're picked up automatically without needing to be enumerated.

An *edge* ``A -> B`` means ``A``'s body references the name ``B``, where
``B`` is itself a node. Self-edges are dropped.

Usage:
    uv run python proof_deps.py halting.py                 # DOT to stdout
    uv run python proof_deps.py halting.py -o deps.dot
    uv run python proof_deps.py halting.py -o deps.svg --render
"""

import argparse
import ast
import subprocess
import sys
from pathlib import Path


def _is_proof_decorator(dec: ast.AST) -> bool:
    if isinstance(dec, ast.Call):
        return _is_proof_decorator(dec.func)
    if isinstance(dec, ast.Name):
        return dec.id == "proof"
    if isinstance(dec, ast.Attribute):
        return dec.attr == "proof"
    return False


def collect_nodes(tree) -> dict[str, tuple[ast.AST, bool]]:
    nodes: dict[str, tuple[ast.AST, bool]] = {}
    for stmt in tree.body:
        if isinstance(stmt, ast.FunctionDef):
            is_proof = any(_is_proof_decorator(d) for d in stmt.decorator_list)
            nodes[stmt.name] = (stmt, is_proof)
    return nodes


def references(stmt, universe, self_name):
    out: set[str] = set()
    for sub in ast.walk(stmt):
        if isinstance(sub, ast.Name) and sub.id in universe and sub.id != self_name:
            out.add(sub.id)
    return out


def build_graph(path: Path):
    tree = ast.parse(path.read_text(), filename=str(path))
    nodes = collect_nodes(tree)
    universe = set(nodes)
    proofs = {n for n, (_, is_p) in nodes.items() if is_p}
    raw = {n: references(stmt, universe, n) for n, (stmt, _) in nodes.items()}

    def reach(src):
        seen, out, stack = {src}, set(), list(raw[src])
        while stack:
            n = stack.pop()
            if n in seen:
                continue
            seen.add(n)
            if n in proofs:
                out.add(n)
            else:
                stack.extend(raw[n])
        return out

    return {p: reach(p) for p in proofs}


def to_dot(graph, module_name: str) -> str:
    lines = [
        f'digraph "{module_name}" {{',
        "    rankdir=LR;",
        '    node [shape=box, fontname="monospace", fontsize=10];',
    ]
    for name in sorted(graph):
        lines.append(f'    "{name}";')
    for src in sorted(graph):
        for dst in sorted(graph[src]):
            lines.append(f'    "{src}" -> "{dst}";')
    lines.append("}")
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("module", type=Path, help="Python module to analyse")
    ap.add_argument("-o", "--output", type=Path,
                    help="Output file (default: stdout).")
    ap.add_argument("--render", action="store_true",
                    help="Pipe DOT through ``dot`` and write the rendered "
                         "graph instead. Requires --output; format taken "
                         "from the output suffix (.svg, .png, .pdf, ...).")
    args = ap.parse_args()

    graph = build_graph(args.module)
    dot = to_dot(graph, args.module.stem)

    if args.render:
        if not args.output:
            ap.error("--render requires -o/--output")
        fmt = args.output.suffix.lstrip(".") or "svg"
        subprocess.run(
            ["dot", f"-T{fmt}", "-o", str(args.output)],
            input=dot, text=True, check=True,
        )
    elif args.output:
        args.output.write_text(dot)
    else:
        sys.stdout.write(dot)
    return 0


if __name__ == "__main__":
    sys.exit(main())
