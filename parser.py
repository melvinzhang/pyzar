"""Lark-based parser for HOL terms, with an extensible operator registry.

The parser itself is agnostic about which operators, constants, and types
exist: those are registered by the modules that introduce them.  By the time
you `import nat`, the default signature (`DEFAULT_SIG`) has been populated
transitively:

  - ``axioms.py`` registers ``=``, ``/\\``, ``==>``, ``~``, and the ``bool`` type.
  - ``logic.py``  registers ``\\/``.
  - ``num.py``    registers ``1``, ``SUC``, and the ``num`` type.
  - ``nat.py``    registers ``+``, ``*``, ``>``, ``<``, ``>=``, ``<=``.

Then `parse(...)` works for the chapter-1 surface:

    from parser import parse
    target = parse("(SUC x) * (SUC y) = x * (SUC y) + SUC y")

Adding a new operator is a single registration call in the module that
introduces the kernel constant; nothing in `parser.py` needs to change:

    from parser import add_infix, add_const, parse
    add_infix("-", 50, mk_sub, assoc="left")
    add_const("0", ZERO)
    parse("x - 0 = x")

Or build a private `Signature` and pass it via `parse(s, sig=my_sig)`.

Free variables default to type `num` if a ``num`` type is registered, else
they have no default and `env={name: ty}` (or a kernel term) is required.
"""

import dataclasses
import re

from lark import Lark, LarkError, Token, Tree
from lark.visitors import Interpreter

from fusion import (
    HolError,
    Var, Const, Comb, Abs,
    Tyvar, Tyapp,
    mk_comb, mk_type,
    concl, hyp, new_basic_definition,
)
from basics import mk_app, mk_const, mk_eq, mk_var


class ParseError(Exception):
    pass


# ---------------------------------------------------------------------------
# Assume-pattern AST (surface syntax). Consumed by ``Proof.assume`` to
# destructure the goal antecedent into named facts. New pattern kinds are
# added by extending ``_GRAMMAR`` (the ``pattern`` rule) and registering
# a ``Proof``-level handler via ``proof.register_pattern_handler``.
# ---------------------------------------------------------------------------

@dataclasses.dataclass
class PatName:
    """Atomic pattern: bind the term under ``label`` (anonymous if
    ``label is None``, written ``_`` in source)."""
    label: object   # str | None


@dataclasses.dataclass
class PatConj:
    """Conjunction-split pattern: term must be a right-associated
    conjunction with ``len(parts)`` conjuncts; each sub-pattern receives
    the corresponding conjunct."""
    parts: list   # list of pattern nodes


_SPLICE_RE = re.compile(r"\$\{([A-Za-z_][A-Za-z0-9_]*)\}")


def _is_tyvar_name(name):
    """Surface convention: a single uppercase letter denotes a type
    variable (e.g. ``A``, ``B``); every other identifier must resolve
    to a registered type constructor."""
    return len(name) == 1 and "A" <= name <= "Z"


# ---------------------------------------------------------------------------
# Operator / constant / type registry.
# ---------------------------------------------------------------------------

class Signature:
    """Mutable registry of infix operators, prefix operators, named constants,
    and type names referenced in binder annotations.

    `add_infix(op, prec, builder, assoc="left")`:
        op       -- the operator symbol as it appears in source.
        prec     -- numeric precedence (higher = binds tighter).
        builder  -- ``(lhs_term, rhs_term) -> term``.
        assoc    -- ``"left"``, ``"right"``, or ``"non"``.

    `add_prefix(op, builder)`:
        builder  -- ``term -> term``.

    `add_const(name, term)`:
        Maps a parsed identifier (or numeric literal) directly to a kernel term.

    `add_type(name, ty)`:
        Registers a type name usable in binder annotations like ``!x:num. ...``.

    `add_binder(symbol, wrap)`:
        Registers a binder keyword (``"!"``, ``"?"``, ``"\\"``).
        ``wrap(var, body) -> term`` builds the bound term.
    """
    __slots__ = ("infix", "prefix", "const", "type", "binder", "default_var_ty")

    def __init__(self, default_var_ty=None):
        self.infix  = {}    # op_symbol -> (prec, assoc, builder)
        self.prefix = {}    # op_symbol -> builder
        self.const  = {}    # name      -> kernel term
        self.type   = {}    # type-name -> hol_type
        self.binder = {}    # binder-keyword -> wrap(var, body) -> term
        # The fallback type for a free variable that's neither in `env` nor
        # in `const`.  Set by whoever registers the "default" type (typically
        # `num.py`).  None means "free vars without a type are an error."
        self.default_var_ty = default_var_ty

    def add_infix(self, op, prec, builder, assoc="left"):
        if assoc not in ("left", "right", "non"):
            raise ValueError(f"assoc must be left/right/non, got {assoc!r}")
        self.infix[op] = (prec, assoc, builder)
        self._auto_register_const(op)

    def add_prefix(self, op, builder):
        self.prefix[op] = builder
        self._auto_register_const(op)

    def add_const(self, name, term):
        self.const[name] = term

    def add_type(self, name, ty):
        self.type[name] = ty

    def add_binder(self, symbol, wrap):
        if symbol not in ("!", "?", "\\", "@"):
            raise ValueError(
                f"binder must be one of !, ?, \\\\, @ (got {symbol!r}); "
                "the grammar reserves only those four keywords")
        self.binder[symbol] = wrap

    def _auto_register_const(self, name):
        """Best-effort: store ``mk_const(name, [])`` under `name` in `const`
        so callers can do ``sig[name]`` to recover the kernel constant.
        Silently no-ops if `name` isn't a kernel constant (e.g. registered
        before the kernel const exists, or just a user-chosen pseudo-op)."""
        if name in self.const:
            return
        try:
            self.const[name] = mk_const(name, [])
        except Exception:
            pass

    def __getitem__(self, name):
        """Look up the kernel constant registered under `name`.  Useful for
        `MK_COMB`/`AP_TERM` chains that need the bare const rather than its
        builder."""
        return self.const[name]


DEFAULT_SIG = Signature()


# ---------------------------------------------------------------------------
# Module-level helpers that mutate `DEFAULT_SIG`.  Theory modules import these
# instead of poking the registry object directly, so the cross-module
# interaction surface is just a handful of named functions.
# ---------------------------------------------------------------------------

add_infix  = DEFAULT_SIG.add_infix
add_prefix = DEFAULT_SIG.add_prefix
add_const  = DEFAULT_SIG.add_const
add_type   = DEFAULT_SIG.add_type
add_binder = DEFAULT_SIG.add_binder


def set_default_var_ty(ty):
    """Set the fallback type used when a free variable has no annotation and
    isn't pinned by `env`.  Typically called once by `num.py`."""
    DEFAULT_SIG.default_var_ty = ty


def has_const(name):
    """Whether `name` is registered as a kernel constant in DEFAULT_SIG."""
    return name in DEFAULT_SIG.const


# ---------------------------------------------------------------------------
# Decorators that register the decorated function as a builder for the named
# operator -- syntactic sugar over add_infix/add_prefix/add_binder for the
# common case where the surface metadata sits next to the builder def.
# ---------------------------------------------------------------------------

def infix(op, prec, assoc="left"):
    """Register the decorated ``(lhs, rhs) -> term`` as the infix builder for
    ``op`` at precedence `prec` (higher binds tighter)."""
    def deco(builder):
        add_infix(op, prec, builder, assoc=assoc)
        return builder
    return deco


def prefix(op):
    """Register the decorated ``term -> term`` as the prefix builder for `op`."""
    def deco(builder):
        add_prefix(op, builder)
        return builder
    return deco


def binder(symbol):
    """Register the decorated ``(var, body) -> term`` as the binder for
    `symbol` (one of ``!``, ``?``, ``\\``, ``@``)."""
    def deco(builder):
        add_binder(symbol, builder)
        return builder
    return deco


# ---------------------------------------------------------------------------
# Pretty-printer (display only -- never used by proofs).
#
# Reads infix/prefix/binder operators from the supplied `Signature` so that
# every surface-syntax fact lives in one place.  `\` (raw lambda) is printed
# from its `Abs` shape; `!` and `?` are recognised by their `Comb(Const, Abs)`
# encoding and printed in binder form.
# ---------------------------------------------------------------------------

def pp(tm, sig=None):
    sig = sig or DEFAULT_SIG
    if isinstance(tm, Var):
        return tm.name
    if isinstance(tm, Const):
        return tm.name
    if isinstance(tm, Abs):
        return f"(\\{tm.bvar.name}. {pp(tm.body, sig)})"
    if isinstance(tm, Comb):
        if (isinstance(tm.fun, Const) and tm.fun.name in sig.binder
                and isinstance(tm.arg, Abs)):
            return f"({tm.fun.name}{tm.arg.bvar.name}. {pp(tm.arg.body, sig)})"
        if isinstance(tm.fun, Const) and tm.fun.name in sig.prefix:
            return f"{tm.fun.name}{pp(tm.arg, sig)}"
        if (isinstance(tm.fun, Comb) and isinstance(tm.fun.fun, Const)
                and tm.fun.fun.name in sig.infix):
            op = tm.fun.fun.name
            a = pp(tm.fun.arg, sig)
            b = pp(tm.arg, sig)
            return f"({a} {op} {b})"
        return f"({pp(tm.fun, sig)} {pp(tm.arg, sig)})"
    return repr(tm)


def pp_thm(th, sig=None):
    sig = sig or DEFAULT_SIG
    asl = hyp(th)
    h = "" if not asl else ", ".join(pp(a, sig) for a in asl) + " "
    return f"{h}|- {pp(concl(th), sig)}"


# ---------------------------------------------------------------------------
# Grammar (static -- operator semantics live in the registry, not here).
# ---------------------------------------------------------------------------

_GRAMMAR = r"""
?start: term

label_start: NAME ":" term         -> labelled
           | term                  -> unlabelled

label_or_bare_start: NAME                  -> bare_label
                   | NAME ":" term         -> labelled

let_start: NAME "(" arglist ")" ":=" term -> let_spec_

pattern_start: pattern ":" term    -> pattern_spec_with_term
             | pattern             -> pattern_spec_bare

pattern: NAME                              -> pat_name
       | "(" pattern ("," pattern)+ ")"    -> pat_conj

?type_start: arrow_type

?arrow_type: app_type OP arrow_type        -> arrow_
           | app_type

?app_type: app_type NAME                   -> tapp_
         | atom_type

?atom_type: "(" arrow_type ")"
          | NAME                           -> tname_

?term: binder | infix_chain

binder: "!" varlist "." term       -> forall_
      | "?" varlist "." term       -> exists_
      | "\\" varlist "." term      -> abs_
      | "@" varlist "." term       -> select_

infix_chain: prefix_term (OP rhs_term)*

?rhs_term: binder | prefix_term

?prefix_term: OP prefix_term       -> prefix_app
            | app_term

?app_term: app_term atom            -> app_
         | atom

?atom: "(" term ")"
     | NUM                          -> num_
     | NAME                         -> name

varlist: var_decl+
arglist: var_decl ("," var_decl)*
var_decl: NAME (":" var_type)?

?var_type: atom_type OP var_type           -> arrow_
         | atom_type

NAME: /[A-Za-z_][A-Za-z0-9_]*/
NUM:  /[0-9]+/
OP:   /[+\-*=<>^&|\/\\]+|~/

%ignore /[ \t\r\n]+/
"""

_PARSER = Lark(_GRAMMAR, parser="lalr",
               start=["start", "label_start", "label_or_bare_start",
                      "let_start", "pattern_start", "type_start"])


# ---------------------------------------------------------------------------
# Visitor: builds kernel terms by consulting the registry.
# ---------------------------------------------------------------------------

class _Builder(Interpreter):
    def __init__(self, sig, env):
        super().__init__()
        self.sig = sig
        self.env = dict(env or {})
        self.scope = []          # stack of {name: Var}

    # ----- atom resolution -----

    def _lookup(self, name):
        # Bound variable shadows everything else.
        for s in reversed(self.scope):
            if name in s:
                return s[name]
        # Then registered constants.
        if name in self.sig.const:
            return self.sig.const[name]
        # Then env-provided binding (kernel term or hol_type).
        if name in self.env:
            binding = self.env[name]
            if isinstance(binding, (Var, Const, Comb, Abs)):
                return binding
            return mk_var(name, binding)
        # Otherwise a free variable at the registry's default type.
        ty = self.sig.default_var_ty
        if ty is None:
            raise ParseError(
                f"unknown identifier {name!r} (no default type registered; "
                "pass via `env=` or register a const/default type)")
        return mk_var(name, ty)

    def name(self, tree):
        return self._lookup(str(tree.children[0]))

    def num_(self, tree):
        s = str(tree.children[0])
        if s in self.sig.const:
            return self.sig.const[s]
        raise ParseError(f"unknown numeric literal {s!r}")

    # ----- application + binders -----

    def app_(self, tree):
        f_tree = tree.children[0]
        a_tree = tree.children[1]
        f, a = self.visit(f_tree), self.visit(a_tree)
        return mk_comb(f, a)

    def _decls(self, varlist_tree):
        out = []
        for vd in varlist_tree.children:
            n = str(vd.children[0])
            ty = None
            if len(vd.children) > 1:
                # Explicit type annotation `name : type-expr`.  The
                # type sub-tree dispatches through tname_/tapp_/arrow_,
                # which resolve against the registered signature first
                # and then env-provided type aliases.
                ty = self.visit(vd.children[1])
            elif n in self.env:
                # Inherit type from an env-provided binding so callers can
                # introduce higher-order binders (e.g. !f. ... where
                # f : num -> num) without registering a fresh type alias.
                binding = self.env[n]
                if isinstance(binding, (Tyvar, Tyapp)):
                    ty = binding
                elif isinstance(binding, Var):
                    ty = binding.ty
            if ty is None:
                ty = self.sig.default_var_ty
            if ty is None:
                raise ParseError(
                    f"binder for {n!r} has no type and no default type "
                    "is registered")
            out.append((n, ty))
        return out

    def _binder(self, tree, symbol):
        wrap = self.sig.binder.get(symbol)
        if wrap is None:
            raise ParseError(f"binder {symbol!r} is not registered")
        decls = self._decls(tree.children[0])
        body_tree = tree.children[1]
        scope = {}
        vars_ = []
        for name, ty in decls:
            v = mk_var(name, ty)
            scope[name] = v
            vars_.append(v)
        self.scope.append(scope)
        body = self.visit(body_tree)
        self.scope.pop()
        for v in reversed(vars_):
            body = wrap(v, body)
        return body

    def forall_(self, tree): return self._binder(tree, "!")
    def exists_(self, tree): return self._binder(tree, "?")
    def abs_(self,    tree): return self._binder(tree, "\\")
    def select_(self, tree): return self._binder(tree, "@")

    # ----- spec-form starts (label / let) -----

    def labelled(self, tree):
        label = str(tree.children[0])
        return label, self.visit(tree.children[1])

    def unlabelled(self, tree):
        return None, self.visit(tree.children[0])

    def bare_label(self, tree):
        return str(tree.children[0]), None

    def let_spec_(self, tree):
        name = str(tree.children[0])
        decls = self._decls(tree.children[1])
        bvars = []
        scope = {}
        for nm, ty in decls:
            v = mk_var(nm, ty)
            scope[nm] = v
            bvars.append(v)
        self.scope.append(scope)
        body = self.visit(tree.children[2])
        self.scope.pop()
        return name, bvars, body

    # ----- assume-pattern visitors -----

    def pattern_spec_with_term(self, tree):
        return self.visit(tree.children[0]), self.visit(tree.children[1])

    def pattern_spec_bare(self, tree):
        return self.visit(tree.children[0]), None

    def pat_name(self, tree):
        name = str(tree.children[0])
        return PatName(label=None if name == "_" else name)

    def pat_conj(self, tree):
        return PatConj(parts=[self.visit(c) for c in tree.children])

    # ----- type-expression visitors -----

    def arrow_(self, tree):
        op = str(tree.children[1])
        if op != "->":
            raise ParseError(
                f"expected '->' between types, got {op!r}")
        a = self.visit(tree.children[0])
        b = self.visit(tree.children[2])
        return mk_type("fun", [a, b])

    def tapp_(self, tree):
        arg = self.visit(tree.children[0])
        name = str(tree.children[1])
        # Registered constructors win over the tyvar rule, so a theory
        # that registers a single-letter type (e.g. ``V`` for sets) keeps
        # working.
        if name not in self.sig.type and _is_tyvar_name(name):
            raise ParseError(
                f"{name!r} is a type variable and cannot be applied "
                "as a type constructor")
        try:
            return mk_type(name, [arg])
        except HolError as ex:
            raise ParseError(str(ex)) from ex

    def tname_(self, tree):
        name = str(tree.children[0])
        if name in self.sig.type:
            return self.sig.type[name]
        binding = self.env.get(name)
        if isinstance(binding, (Tyvar, Tyapp)):
            return binding
        if _is_tyvar_name(name):
            return Tyvar(name)
        try:
            return mk_type(name, [])
        except HolError as ex:
            raise ParseError(str(ex)) from ex

    # ----- prefix + flat infix chain -----

    def prefix_app(self, tree):
        op = str(tree.children[0])
        builder = self.sig.prefix.get(op)
        if builder is None:
            raise ParseError(f"unknown prefix operator {op!r}")
        return builder(self.visit(tree.children[1]))

    def infix_chain(self, tree):
        children = tree.children
        if len(children) == 1:
            return self.visit(children[0])
        terms = [self.visit(children[0])]
        ops = []
        for i in range(1, len(children), 2):
            op = str(children[i])
            meta = self.sig.infix.get(op)
            if meta is None:
                raise ParseError(f"unknown infix operator {op!r}")
            ops.append((op, *meta))           # (op, prec, assoc, builder)
            terms.append(self.visit(children[i + 1]))
        return _climb(terms, ops)


def _climb(terms, ops):
    """Precedence-climbing reducer for a flat infix chain.

    `terms`: N kernel terms.   `ops`: N-1 tuples ``(op, prec, assoc, builder)``.
    """
    out = [terms[0]]
    op_stack = []

    def reduce_top():
        op, prec, assoc, builder = op_stack.pop()
        rhs = out.pop()
        lhs = out.pop()
        out.append(builder(lhs, rhs))

    for (op, prec, assoc, builder), rhs in zip(ops, terms[1:]):
        while op_stack:
            top_op, top_prec, top_assoc, _ = op_stack[-1]
            if top_prec > prec or (top_prec == prec and top_assoc == "left"):
                reduce_top()
                continue
            if top_prec == prec and top_assoc == "non":
                raise ParseError(
                    f"non-associative operator {op!r} cannot chain with {top_op!r}")
            break
        out.append(rhs)
        op_stack.append((op, prec, assoc, builder))

    while op_stack:
        reduce_top()
    return out[0]


# ---------------------------------------------------------------------------
# Public API.
# ---------------------------------------------------------------------------

def _splice(s, _env_bindings, bindings):
    """Antiquote substitution. Returns ``(s_after_splice, merged_env,
    name_to_sentinel)``: the input string with ``${name}`` replaced by
    fresh sentinel idents, the merged parser env including those
    sentinels, and the original-name → sentinel mapping (used by the
    post-parse unused-binding check)."""
    env_b = _env_bindings or {}
    name_to_sentinel = {}
    splice_env = {}

    def _repl(m):
        name = m.group(1)
        if name in bindings:
            value = bindings[name]
        elif name in env_b:
            value = env_b[name]
        else:
            raise ParseError(
                f"antiquote ${{{name}}} has no binding "
                f"(pass {name}=... to parse)")
        if name not in name_to_sentinel:
            sentinel = f"__splice{len(name_to_sentinel)}_{name}__"
            name_to_sentinel[name] = sentinel
            splice_env[sentinel] = value
        return name_to_sentinel[name]

    s2 = _SPLICE_RE.sub(_repl, s)
    return s2, {**env_b, **bindings, **splice_env}, name_to_sentinel


def _walk_name_tokens(tree):
    """Yield every ``NAME`` token's string value found in ``tree``."""
    stack = [tree]
    while stack:
        node = stack.pop()
        if isinstance(node, Tree):
            stack.extend(node.children)
        elif isinstance(node, Token) and node.type == "NAME":
            yield str(node)


def _check_unused_bindings(tree, bindings, name_to_sentinel):
    """Raise ``ParseError`` if any kwarg in ``bindings`` is unreferenced
    (neither as a bare ``NAME`` in the parse tree nor as ``${name}``)."""
    if not bindings:
        return
    sentinel_set = set(name_to_sentinel.values())
    bare_names = set(_walk_name_tokens(tree)) - sentinel_set
    referenced = set(name_to_sentinel) | (set(bindings) & bare_names)
    unused = set(bindings) - referenced
    if unused:
        raise ParseError(
            f"unused binding(s): {sorted(unused)} "
            "(neither bare name nor ${{...}} reference appears in source)")


def _lark_parse(s, start):
    """Run the Lark parser and rewrap lexer/parser errors as
    ``ParseError`` so callers don't have to know about lark."""
    try:
        return _PARSER.parse(s, start=start)
    except LarkError as ex:
        raise ParseError(str(ex)) from ex


def _run_parse(s, start, sig, _env_bindings, bindings):
    """Splice → parse → unused-binding check → visit. Shared spine for
    every public ``parse_*`` entry point."""
    s2, merged, name_to_sentinel = _splice(s, _env_bindings, bindings)
    tree = _lark_parse(s2, start)
    _check_unused_bindings(tree, bindings, name_to_sentinel)
    return _Builder(sig or DEFAULT_SIG, merged).visit(tree)


def parse(s, sig=None, _env_bindings=None, **bindings):
    """Parse `s` into a kernel term.

    `bindings` (kwargs) maps free-variable names to either their
    ``hol_type`` (when the default isn't right) or directly to a kernel
    term to substitute.  Two reference styles in `s`:

      - bare ``name``  -- resolves through scope > const > bindings > default.
        Falls through to a default-typed free var if unbound.
      - ``${name}``    -- requires `name` to be in bindings; raises
        `ParseError` if missing.

    Every kwarg in `bindings` must be referenced (either as a bare ``name``
    appearing in `s` or as ``${name}``); unused bindings raise `ParseError`.

    `sig` is a `Signature`; defaults to `DEFAULT_SIG`.

    `_env_bindings` is private: callers (e.g. `Proof._parse`) use it to
    pass long-lived bindings that bypass the unused check.
    """
    return _run_parse(s, "start", sig, _env_bindings, bindings)


def parse_label(s, sig=None, _env_bindings=None, **bindings):
    """Parse ``"label: term"`` or bare ``"term"``.

    Returns ``(label_or_None, kernel_term)``. The label form is
    structurally unambiguous (a term cannot start with ``IDENT:`` --
    binders open with ``!`` / ``?`` / ``\\`` / ``@``), so the grammar
    commits once it sees ``NAME ":"``: a body-level ``ParseError``
    propagates rather than triggering a misleading whole-spec retry.
    """
    return _run_parse(s, "label_start", sig, _env_bindings, bindings)


def parse_label_or_bare(s, sig=None, _env_bindings=None, **bindings):
    """Parse ``"label"`` or ``"label: term"`` (no bare-term form).

    Returns ``(label, term_or_None)``: ``term`` is ``None`` for the
    bare-label form, or the parsed kernel body otherwise. Used by
    tactics (``suppose`` / ``by_contradiction``) where a bare
    identifier means "use this as the label, body is implicit"; an
    explicit form lets the caller verify the body against an
    expected hypothesis.
    """
    return _run_parse(
        s, "label_or_bare_start", sig, _env_bindings, bindings)


_LABEL_PEEL_RE = re.compile(r"^\s*([A-Za-z_]\w*)\s*:(?!=)\s*(.*)$", re.DOTALL)


def peel_label_prefix(spec):
    """Structural-only split of ``"label: rest"`` -- returns
    ``(label, rest_str)`` or ``None`` if the spec has no leading label.

    The ``label:`` form is structurally unambiguous (see ``parse_label``);
    this helper exists for the rare case where the body must be parsed
    lazily because its env depends on the about-to-be-bound label (e.g.
    ``Proof.choose``'s ``"name: equation"`` form, where ``name`` is a
    parser binding consumed by the equation parse). Callers that can
    parse eagerly should prefer ``parse_label``.
    """
    m = _LABEL_PEEL_RE.match(spec)
    return (m.group(1), m.group(2)) if m else None


def parse_let_spec(s, sig=None, _env_bindings=None, **bindings):
    """Parse ``"NAME(arg1, arg2, ...) := body"``.

    Returns ``(name, [Var, ...], body_term)``. Each arg may carry an
    optional type annotation ``arg : type-expr`` (any arrow_type, with
    parens around postfix application); names inside the type resolve
    against ``sig.type`` first, then env-provided type aliases, then
    inherited types from env-provided ``Var`` bindings, and finally
    the registry's default-var type. The body is parsed with all args
    in scope.
    """
    return _run_parse(s, "let_start", sig, _env_bindings, bindings)


def parse_pattern_spec(s, sig=None, _env_bindings=None, **bindings):
    """Parse ``"pattern: term"`` or ``"pattern"`` (assume-spec form).

    Returns ``(pattern, term_or_None)``. ``pattern`` is a tree of
    ``PatName`` / ``PatConj`` nodes; ``term`` is the parsed kernel
    term body (or ``None`` when the spec carries no body). The body
    is parsed in the supplied scope so identifiers introduced by
    earlier ``fix``/``choose``/``let`` resolve correctly.

    The grammar:
        pattern_start := pattern (":" term)?
        pattern       := NAME                              # PatName
                       | "(" pattern ("," pattern)+ ")"    # PatConj (>= 2 parts)
    """
    return _run_parse(s, "pattern_start", sig, _env_bindings, bindings)


def parse_type(s, sig=None):
    """Parse a type expression into a kernel ``hol_type``.

    Surface syntax:

      - ``bool``, ``num``        -- registered type constructors (0-ary).
      - ``A``, ``B``, ...        -- single uppercase letter = ``Tyvar``,
                                    *unless* the same name is registered
                                    as a type (e.g. ``V`` in set theory),
                                    in which case the registration wins.
      - ``T1 -> T2``             -- right-associative function type.
      - ``T name``               -- postfix unary application
                                    (e.g. ``num list`` once ``list`` is
                                    introduced).
      - ``(T)``                  -- grouping.

    Multi-argument constructors aren't yet wired up; build those with
    ``mk_type`` directly until the surface need shows up.
    """
    sig = sig or DEFAULT_SIG
    tree = _lark_parse(s, "type_start")
    return _Builder(sig, {}).visit(tree)


def define(name, ty, body, *, sig=None,
           prec=None, assoc=None, prefix=False, **bindings):
    """Introduce a new defined constant.

    Parameters:
      name -- the constant's surface name (e.g. ``">"`` or ``"+"``).
      ty   -- the constant's type, either a string (parsed via
              `parse_type(ty, sig=sig)`) or a pre-built `hol_type`.
      body -- the definition's right-hand side, either a string (parsed
              via `parse(body, sig=sig, **bindings)`) or a pre-built
              kernel term.
      sig  -- target `Signature`; defaults to `DEFAULT_SIG`.
      prec, assoc -- if given, also register as an infix operator
              (`assoc` in {"left","right","non"}).
      prefix -- if True, also register as a unary prefix operator
              (mutually exclusive with `prec`/`assoc`).
      bindings -- forwarded to `parse` (free-variable type pins, type
              aliases, antiquotes); ignored if `body` is already a term.

    Side effects (on success):
      * calls `new_basic_definition` to introduce the constant;
      * registers ``name -> mk_const(name, [])`` in `sig.const`;
      * if `prec`/`assoc`: registers as infix in `sig` (which is also
        what the printer reads from);
      * if `prefix=True`: registers as prefix in `sig`.

    Returns the definition theorem ``|- name = body``.
    """
    sig = sig or DEFAULT_SIG
    if isinstance(ty, str):
        ty = parse_type(ty, sig=sig)
    if isinstance(body, str):
        rhs = parse(body, sig=sig, **bindings)
    else:
        if bindings:
            raise ValueError(
                f"define({name!r}): bindings given but body is already a term")
        rhs = body
    if prefix and (prec is not None or assoc is not None):
        raise ValueError(
            f"define({name!r}): prefix=True is mutually exclusive with prec/assoc")
    def_th = new_basic_definition(mk_eq(Var(name, ty), rhs))
    const = mk_const(name, [])
    sig.add_const(name, const)
    if prec is not None:
        if assoc is None:
            raise ValueError(
                f"define({name!r}): prec given but assoc missing")
        def infix_builder(a, b):
            return mk_app(const, a, b)
        sig.add_infix(name, prec, infix_builder, assoc=assoc)
    if prefix:
        def prefix_builder(t):
            return mk_comb(const, t)
        sig.add_prefix(name, prefix_builder)
    return def_th
