# ---------------------------------------------------------------------------
# PRST kernel-term builders (Tier 1).
#
# Readable construction helpers for the deeply-nested PR-symbol terms
# that show up in numeral_pr / substitute_pr / diag_pr / Proof_PRST_pr
# bodies. Each helper returns a kernel `term`; feed the result directly
# to `parser.define(name, ty, body_term)` -- the parser accepts terms
# as bodies, skipping the string-parse step entirely.
#
# Builder catalogue:
#
#     nat(k)       SUC0^k 0 nat0 literal
#     pt_list(*x)  Tup_pt-cons list of the args (Empty_pt-terminated)
#     proj(i, n)   proj_sym (nat i) (nat n)
#     rec(g, h)    rec_sym g h
#     comp(g,*as)  comp_sym g (pt_list *as)
#     app_pt(fn,*as)
#                  App_pt fn (pt_list *as)
#     var_t(i)     Var_t (nat i)
#     var_pt(v)    Var_pt v          (v already a term)
#     tup_pt(a,b)  Tup_pt a b        (binary cons cell, not a list)
#     adj_pt(a,b)  Adj_pt a b
#     eq_pf(a,b)   Eq_pf a b
#     in_pa(a,b)   In_pa a b
#     not_pf(a)    Not_pf a
#     imp_pf(a,b)  Imp_pf a b
#
# Before / after example for numeral_pr_def's body string:
#
#     "rec_sym zero_sym "
#     "  (comp_sym adj_sym "
#     "    (Tup_pt (proj_sym (SUC0 (SUC0 0)) (SUC0 (SUC0 (SUC0 (SUC0 0))))) "
#     "      (Tup_pt (proj_sym (SUC0 (SUC0 0)) (SUC0 (SUC0 (SUC0 (SUC0 0))))) "
#     "        Empty_pt)))"
#
#       --->
#
#     rec(ZERO_SYM, comp(ADJ_SYM, proj(2, 4), proj(2, 4)))
#
# Constants are loaded lazily to avoid circular imports: prst_pr_builders
# is meant to be imported *into* prst_pr (which defines zero_sym /
# adj_sym / ...), so the constants get resolved on first access via
# `mk_const(name, [])`.
# ---------------------------------------------------------------------------

from basics import mk_app, mk_const

# Bare nat0 / encoding constants (always available -- predefined in basics
# or nat0 modules, no prst_pr dependency).
ZERO    = mk_const("0", [])
SUC0    = mk_const("SUC0", [])
PAIR_ORD = mk_const("Pair_ord", [])

# PRST term constructors -- live in prst_syntax / prst_pr but the
# *constants* are already registered by the time this module is imported.
EMPTY_PT = mk_const("Empty_pt", [])
TUP_PT   = mk_const("Tup_pt", [])
VAR_T    = mk_const("Var_t", [])
VAR_PT   = mk_const("Var_pt", [])
APP_PT   = mk_const("App_pt", [])

# PR-symbol constants -- defined in prst_pr; the *names* are known here,
# resolved via mk_const at use time. Wrapped in functions so a stale
# import order at module load doesn't matter; the kernel only enforces
# "constant exists" at the moment of mk_const evaluation.
def _c(name: str):
    return mk_const(name, [])


# ---------------------------------------------------------------------------
# Nat0 literal builder.
# ---------------------------------------------------------------------------


def nat(k: int):
    """Build the nat0 literal ``SUC0^k 0``.

    Examples: ``nat(0) == 0``, ``nat(2) == SUC0 (SUC0 0)``.

    Beats the SUC0-stack incantation `SUC0 (SUC0 (SUC0 (SUC0 0)))` for
    every literal beyond `nat(2)`. For PR-symbol argument positions
    `proj_sym i n` where both i and n are small literals, `nat(i)` /
    `nat(n)` collapse the inner padding.
    """
    if k < 0:
        raise ValueError(f"nat({k}): negative literal")
    t = ZERO
    for _ in range(k):
        t = mk_app(SUC0, t)
    return t


# ---------------------------------------------------------------------------
# Tup_pt cons list.
# ---------------------------------------------------------------------------


def pt_list(*items):
    """Build the Tup_pt-cons list ``Tup_pt h1 (Tup_pt h2 (... Empty_pt))``.

    ``pt_list()`` returns ``Empty_pt``.
    ``pt_list(a, b, c)`` returns ``Tup_pt a (Tup_pt b (Tup_pt c Empty_pt))``.

    The bare binary cons ``Tup_pt a b`` (no Empty_pt terminator) is
    `tup_pt(a, b)` below -- distinct from `pt_list(a, b)`, which adds
    the terminator. Use `pt_list` for PR-symbol arg vectors and
    `tup_pt` for binary cons cells in formula syntax.
    """
    out = EMPTY_PT
    for a in reversed(items):
        out = mk_app(TUP_PT, a, out)
    return out


# ---------------------------------------------------------------------------
# Binary constructors (formula-syntax cons cells).
# ---------------------------------------------------------------------------


def tup_pt(a, b):
    """``Tup_pt a b`` -- binary cons cell (not a list)."""
    return mk_app(TUP_PT, a, b)


def adj_pt(a, b):
    """``Adj_pt a b``."""
    return mk_app(_c("Adj_pt"), a, b)


def eq_pf(a, b):
    """``Eq_pf a b``."""
    return mk_app(_c("Eq_pf"), a, b)


def in_pa(a, b):
    """``In_pa a b``."""
    return mk_app(_c("In_pa"), a, b)


def not_pf(a):
    """``Not_pf a``."""
    return mk_app(_c("Not_pf"), a)


def imp_pf(a, b):
    """``Imp_pf a b``."""
    return mk_app(_c("Imp_pf"), a, b)


def var_pt(v):
    """``Var_pt v`` -- v is a term (often `nat(k)` or a free Var)."""
    return mk_app(VAR_PT, v)


def var_t(i: int):
    """``Var_t (nat i)`` -- meta-level variable indexed by an integer.

    The arg-list slot of proj/rec defining axioms uses Var_t i for
    the i-th free index; integers are the readable surface."""
    return mk_app(VAR_T, nat(i))


def app_pt(fn, *args):
    """``App_pt fn (pt_list *args)`` -- common shape inside axiom bodies."""
    return mk_app(APP_PT, fn, pt_list(*args))


def pair_ord(a, b):
    """``Pair_ord a b`` -- bare encoding cons (used for raw tag manipulation
    when bypassing the named constructors)."""
    return mk_app(PAIR_ORD, a, b)


# ---------------------------------------------------------------------------
# PR-symbol builders.
# ---------------------------------------------------------------------------


def proj(i: int, n: int):
    """``proj_sym (nat i) (nat n)`` -- i-th projection of n args.

    Convention: ``proj 0 n`` extracts the first arg, ``proj (n-1) n``
    extracts the last. Soundness obligation: ``nat0_lt i n``.
    """
    return mk_app(_c("proj_sym"), nat(i), nat(n))


def proj_t(i, n):
    """``proj_sym i n`` -- variant for non-literal i / n (already terms)."""
    return mk_app(_c("proj_sym"), i, n)


def rec(g, h):
    """``rec_sym g h`` -- primitive recursion: g is the base, h is the step.

    Standard equations (via PR-defining axioms):
      rec_sym g h zero_sym         args = g args
      rec_sym g h (Adj_pt i s)     args = h (i, s, rec_sym g h s args, args).
    """
    return mk_app(_c("rec_sym"), g, h)


def course_rec(g, h):
    """``course_rec_sym g h`` -- structural recursion on Pair_ord-decomposition.

    Defining equations (via PR-defining axioms):
      course_rec g h [0]           = g []
      course_rec g h [Pair_ord a b]
          = h [a; b; course_rec g h [a]; course_rec g h [b]].

    The step `h` receives the left/right components AND the recursive
    values at each, so structural recursion on formula trees /
    proof lists / etc. is a ~20-line composition without needing
    separate pair_left / pair_right / get_tag primitives.
    """
    return mk_app(_c("course_rec_sym"), g, h)


def comp(g, *args):
    """``comp_sym g (pt_list *args)`` -- composition.

    Reading: apply ``g`` to the tuple ``[h1 args; h2 args; ...; hk args]``,
    where each ``hi`` is a PR symbol (already encoded as a nat0 term).
    The args-list of comp_sym is itself a Tup_pt cons list.
    """
    return mk_app(_c("comp_sym"), g, pt_list(*args))


def comp_t(g, args_tup):
    """``comp_sym g args_tup`` -- variant for a pre-built args tuple."""
    return mk_app(_c("comp_sym"), g, args_tup)


def if_in(test, t_val, x_branch, y_branch):
    """``App_pt-shape input for if_in_sym``. Reads as:
    "if test ∈ t_val then x_branch else y_branch."

    Note: this builds the App_pt-style application -- the 4-tuple of
    args to if_in_sym -- not a closed PR symbol. Use inside comp() to
    package as a PR symbol.
    """
    return pt_list(test, t_val, x_branch, y_branch)


# ---------------------------------------------------------------------------
# Symbolic-name shortcuts (loaded as terms, not constants).
# ---------------------------------------------------------------------------


def zero_sym():    return _c("zero_sym")
def adj_sym():     return _c("adj_sym")
def if_in_sym():   return _c("if_in_sym")
def mu_sym(f):     return mk_app(_c("mu_sym"), f)
