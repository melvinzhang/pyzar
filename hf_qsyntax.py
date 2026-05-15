"""Quoted HF-syntax parser.

This module parses a deliberately small grammar for HF syntax *as data*.
It is separate from ``parser.parse`` because the surface strings have a
different meaning here:

    qparse("Var_t(var_z)", var_z=tm)

returns the quoted HF-set code for the syntax node ``Var_t`` with payload
``tm``.  It does not return the primitive HOL term ``Var_t tm``.

The intended consumer is a quoted-data/template layer: object-language
``substitute`` keeps its usual variable-substitution semantics, while
template filling walks these emitted ``Empty_t``/``Insert_t`` data towers.
"""

from __future__ import annotations

from lark import Lark, LarkError, Token, Tree

from basics import mk_app
from fusion import HolError
from hf_syntax import Empty_t, Insert_t


_GRAMMAR = r"""
?start: expr
?expr: call
     | atom

call: NAME "(" [args] ")"
args: expr ("," expr)*

?atom: NAME        -> name
     | INT         -> int_lit

%import common.CNAME -> NAME
%import common.INT
%import common.WS_INLINE
%ignore WS_INLINE
"""


_PARSER = Lark(_GRAMMAR, parser="lalr", start="start")


class QParseError(HolError):
    pass


def _app(f, *args):
    out = f
    for arg in args:
        out = mk_app(out, arg)
    return out


def quote_hf_lit(n: int):
    """Closed HF quote of the Python nat ``n`` used in syntax data.

    This is the finite, fully expanded counterpart of ``quote_hf n``.
    It is intentionally not the von Neumann ordinal numeral for ``n``:
    syntax codes are HF sets, so constructor tags must be inserted as
    their Ackermann/HF-set quotes.
    """
    if n < 0:
        raise QParseError(f"qparse: negative numeral {n} is not allowed")
    if n == 0:
        return Empty_t
    low = (n & -n).bit_length() - 1
    clear = n & ~(1 << low)
    return _app(Insert_t, quote_hf_lit(low), quote_hf_lit(clear))


# Backwards-compatible name for callers that only need a closed qparse atom.
quote_nat = quote_hf_lit


def q_pair_ord(a, b):
    """Kuratowski ``Pair_ord a b`` expanded in HF set primitives."""
    sing_a = _app(Insert_t, a, Empty_t)
    pair_ab = _app(Insert_t, a, _app(Insert_t, b, Empty_t))
    return _app(Insert_t, sing_a, _app(Insert_t, pair_ab, Empty_t))


def q_var_t(v):
    return q_pair_ord(quote_hf_lit(2), v)


def q_eq_f(a, b):
    return q_pair_ord(quote_hf_lit(5), q_pair_ord(a, b))


def q_not_f(phi):
    return q_pair_ord(quote_hf_lit(6), phi)


def q_imp_f(phi, psi):
    return q_pair_ord(quote_hf_lit(7), q_pair_ord(phi, psi))


def q_forall_f(v, phi):
    return q_pair_ord(quote_hf_lit(8), q_pair_ord(v, phi))


def q_insert_t(a, b):
    return q_pair_ord(quote_hf_lit(9), q_pair_ord(a, b))


def q_in_a(a, b):
    return q_pair_ord(quote_hf_lit(10), q_pair_ord(a, b))


_CTORS = {
    "Pair_ord": (2, q_pair_ord),
    "Var_t": (1, q_var_t),
    "Eq_f": (2, q_eq_f),
    "Not_f": (1, q_not_f),
    "Imp_f": (2, q_imp_f),
    "Forall_f": (2, q_forall_f),
    "Insert_t": (2, q_insert_t),
    "In_a": (2, q_in_a),
}


def _flatten_args(node):
    if isinstance(node, Tree) and node.data == "args":
        return list(node.children)
    return [node]


def _build(node, env):
    if isinstance(node, Token):
        if node.type == "NAME":
            name = str(node)
            if name == "Empty_t":
                return Empty_t
            if name in env:
                return env[name]
            raise QParseError(f"qparse: unknown quoted-syntax leaf {name!r}")
        if node.type == "INT":
            return quote_hf_lit(int(str(node)))

    if not isinstance(node, Tree):
        raise QParseError(f"qparse: unexpected parser node {node!r}")

    if node.data == "name":
        return _build(node.children[0], env)

    if node.data == "int_lit":
        return _build(node.children[0], env)

    if node.data == "call":
        name = str(node.children[0])
        if name not in _CTORS:
            raise QParseError(f"qparse: unknown quoted-syntax constructor {name!r}")
        arity, builder = _CTORS[name]
        arg_nodes = []
        if len(node.children) == 2:
            arg_nodes = _flatten_args(node.children[1])
        if len(arg_nodes) != arity:
            raise QParseError(
                f"qparse: {name} expects {arity} argument(s), got {len(arg_nodes)}"
            )
        return builder(*[_build(arg, env) for arg in arg_nodes])

    raise QParseError(f"qparse: unsupported grammar node {node.data!r}")


def qparse(source: str, _env_bindings=None, **bindings):
    """Parse quoted HF syntax data into an expanded HF-set term.

    Bare names are either ``Empty_t`` or entries supplied in ``bindings`` /
    ``_env_bindings``.  Integer literals are closed HF numerals.  Constructor
    calls are quoted data constructors, not primitive HOL constructor
    applications.
    """
    env = {}
    if _env_bindings:
        env.update(_env_bindings)
    env.update(bindings)
    try:
        tree = _PARSER.parse(source)
    except LarkError as exc:
        raise QParseError(f"qparse: failed to parse {source!r}: {exc}") from exc
    return _build(tree, env)
