"""Tarski-Grothendieck set theory on top of the HOL kernel.

Introduces a base type ``V`` of sets, a membership predicate
``In : V -> V -> bool``, the usual ZF axioms (extensionality, foundation,
pairing, union, powerset, replacement, infinity), and Tarski's Axiom A
asserting that every set is contained in a Grothendieck universe. Choice
is derivable from Axiom A, so it is not posted separately; the resulting
theory is ZFC + universes (= TG).

Run ``uv run python tg_set_theory.py`` to load the development; the kernel
type-checks every axiom statement and rejects any ill-formed term.
"""

from fusion import (
    Var, bool_ty, mk_type, new_type, new_constant, new_axiom,
    ASSUME, EQ_MP, DEDUCT_ANTISYM_RULE,
)
from basics import mk_fun_ty, mk_const, mk_abs, mk_app
from parser import (
    add_const, add_type, set_default_var_ty, parse, define, pp_thm,
)
import axioms  # noqa: F401 -- registers !, ?, /\, \/, ==>, ~, @, =, T, F
from axioms import mk_select, mk_forall, mk_exists, mk_imp
from tactics import (
    SPEC, SPECL, GEN, GENL, DISCH, MP, EXISTS, AP_TERM, AP_THM, SYM,
    BETA_CONV, CHOOSE_WITNESS, CONJUNCT1, CONJUNCT2, UNFOLD,
)
from basics import dest_eq  # for occasional shape checks
from axioms import dest_imp, dest_forall
from proof import proof


# ---------------------------------------------------------------------------
# Base type V and membership In
# ---------------------------------------------------------------------------

new_type("V", 0)
V = mk_type("V", [])
add_type("V", V)
set_default_var_ty(V)

new_constant("In", mk_fun_ty(V, mk_fun_ty(V, bool_ty)))
In = mk_const("In", [])
add_const("In", In)

# Class functions V -> V are heavy use; expose the type as a parser alias
# so axiom bodies can write ``?f:VV. ...``.
VV = mk_fun_ty(V, V)


# ---------------------------------------------------------------------------
# Subset, transitive set, equinumerosity (size comparison via class function)
# ---------------------------------------------------------------------------

# Subset s t  <=>  every element of s is an element of t.
SUBSET_DEF = define(
    "Subset", mk_fun_ty(V, mk_fun_ty(V, bool_ty)),
    "\\s t. !x. In x s ==> In x t")

# Trans u  <=>  every member of u is also a subset of u (transitive set).
TRANS_DEF = define(
    "Trans", mk_fun_ty(V, bool_ty),
    "\\u. !x. In x u ==> Subset x u")

# Equinum a b  <=>  there is a class function f : V -> V whose restriction
# to a is a bijection onto b. Standard HOL-ZF encoding -- f is a
# meta-level function, not an internal set-theoretic graph.
EQUINUM_DEF = define(
    "Equinum", mk_fun_ty(V, mk_fun_ty(V, bool_ty)),
    parse(
        "\\a b. ?f:VV. "
        "(!x. In x a ==> In (f x) b) /\\ "
        "(!x y. In x a /\\ In y a /\\ f x = f y ==> x = y) /\\ "
        "(!y. In y b ==> ?x. In x a /\\ f x = y)",
        VV=VV))


# ---------------------------------------------------------------------------
# ZF axioms
# ---------------------------------------------------------------------------

# Extensionality: sets with the same members are equal.
EXTENSIONALITY = new_axiom(parse(
    "!a b. (!x. In x a = In x b) ==> a = b"))

# Foundation: every nonempty set has an element disjoint from it.
FOUNDATION = new_axiom(parse(
    "!a. (?x. In x a) ==> (?x. In x a /\\ ~(?y. In y a /\\ In y x))"))

# Pairing: for any two sets there is a set whose members are exactly them.
PAIRING = new_axiom(parse(
    "!a b. ?p. !x. In x p = (x = a \\/ x = b)"))

# Union: for any set a, the union of its members exists as a set.
UNION = new_axiom(parse(
    "!a. ?u. !x. In x u = (?y. In x y /\\ In y a)"))

# Powerset: for any set a, the set of subsets of a exists.
POWERSET = new_axiom(parse(
    "!a. ?p. !x. In x p = Subset x a"))

# Replacement: if R is functional on a, then the R-image of a is a set.
# Functionality is the explicit "at most one image" condition; we don't
# need a unique-existential constant.
RR = mk_fun_ty(V, mk_fun_ty(V, bool_ty))
REPLACEMENT = new_axiom(parse(
    "!a. (!x y1 y2. In x a /\\ R x y1 /\\ R x y2 ==> y1 = y2) ==> "
    "(?b. !y. In y b = (?x. In x a /\\ R x y))",
    R=RR))

# Infinity: an inductive set exists -- it contains an empty set and is
# closed under x |-> x u {x}. Stated unfolded so we don't yet need
# constants for empty / successor.
INFINITY = new_axiom(parse(
    "?I. (?z. In z I /\\ ~(?w. In w z)) /\\ "
    "(!x. In x I ==> (?y. In y I /\\ (!w. In w y = (In w x \\/ w = x))))"))


# ---------------------------------------------------------------------------
# Tarski's Axiom A: every set is contained in a Grothendieck universe.
#
# A "universe" U is transitive, closed under powerset-membership (every
# member has its powerset in U), and reflects size (every subset of U is
# either equinumerous with U or itself a member of U). Closure under
# binary union follows; together these clauses say U is a set-model of
# ZFC, i.e. a strongly inaccessible level of the cumulative hierarchy.
#
# Iterating this gives a proper class of inaccessibles. Choice is a
# corollary (well-order any set via the ordinal structure of a containing
# universe), so we don't post it separately. ZF + A = TG.
# ---------------------------------------------------------------------------

TARSKI_A = new_axiom(parse(
    "!x. ?u. In x u /\\ Trans u /\\ "
    "(!y. In y u ==> (?p. In p u /\\ (!z. In z p = Subset z y))) /\\ "
    "(!Y. Subset Y u ==> Equinum Y u \\/ In Y u)"))


# ---------------------------------------------------------------------------
# Class-function form of the axiom of choice.
#
# This form is the "easy" choice statement: it asserts a meta-level
# function f : V -> V whose value at each non-empty x in X is a member of
# x. It follows directly from HOL's Hilbert select (SELECT_AX) -- the
# witness is the literal class function ``\x. @y. In y x``. It does NOT
# use Tarski A or any ZF axiom.
#
# The "hard" choice statements (an internal set of ordered pairs serving
# as a choice function; equivalently, every set is well-orderable) are
# what genuinely need Tarski A. Proving them requires building ordered
# pairs, separation, ordinals, Hartogs' theorem, and the well-ordering
# transfer -- a substantial ZF formalisation that this file does not
# attempt. Tarski 1939 is the reference.
# ---------------------------------------------------------------------------

# Promote the meta-level choice function to a real kernel constant so the
# DSL can witness with it (no beta-redex visible in the substituted goal).
CHOOSE_DEF = define("Choose", VV, "\\x. @y. In y x")


def FOLD_CHOOSE(y0_eq):
    """``|- In (@y. In y x) x``  =>  ``|- In (Choose x) x``.

    Folds the SELECT-witness back through CHOOSE_DEF. ``x`` is read off
    the input theorem's conclusion so the helper carries no extra args."""
    x_t = y0_eq._concl.arg
    eq = UNFOLD(CHOOSE_DEF, x_t)               # |- Choose x = @y. In y x
    lift = AP_THM(AP_TERM(In, eq), x_t)        # |- In (Choose x) x = In (@y. In y x) x
    return EQ_MP(SYM(lift), y0_eq)


@proof
def CLASS_AC(p):
    p.goal(
        "!X. (!x. In x X ==> ?y. In y x) ==> (?f:VV. !x. In x X ==> In (f x) x)",
        types={"VV": VV})
    p.fix("X")
    p.assume("hX: !x. In x X ==> ?y. In y x")
    with p.have("hChoose: !x. In x X ==> In (Choose x) x").proof():
        p.fix("x")
        p.assume("hx: In x X")
        p.have("hex: ?y. In y x").by_match("hX", "hx")
        p.choose("y0: In y0 x", from_="hex")
        p.thus("In (Choose x) x").by(FOLD_CHOOSE, "y0_eq")
    p.thus("?f:VV. !x. In x X ==> In (f x) x").by_witness("Choose", "hChoose")


# ---------------------------------------------------------------------------
# Subset antisymmetry: mutually-included sets are equal.
#
# A canonical pairing of EXTENSIONALITY with the SUBSET definition. The
# proof is short and uses no kernel machinery beyond basic boolean rules
# plus DEDUCT_ANTISYM_RULE (the iff-intro that turns ``p ==> q`` and
# ``q ==> p`` into ``p = q``).
# ---------------------------------------------------------------------------

def GEN_IFF(th_fab, th_fba):
    """``|- !x. P x ==> Q x``, ``|- !x. Q x ==> P x``  =>  ``|- !x. P x = Q x``.

    Iff-intro under a leading universal. Uses ``DEDUCT_ANTISYM_RULE`` after
    crossing the two implications under ASSUMEd antecedents."""
    pred = dest_forall(th_fab._concl)
    x = pred.bvar
    th_pq = SPEC(x, th_fab)
    th_qp = SPEC(x, th_fba)
    p_t, _ = dest_imp(th_pq._concl)
    q_t, _ = dest_imp(th_qp._concl)
    th_q = MP(th_pq, ASSUME(p_t))
    th_p = MP(th_qp, ASSUME(q_t))
    return GEN(x, SYM(DEDUCT_ANTISYM_RULE(th_q, th_p)))


@proof
def SUBSET_ANTISYM(p):
    p.goal("!a b. Subset a b /\\ Subset b a ==> a = b")
    p.fix("a b")
    p.assume("(h1, h2): Subset a b /\\ Subset b a")
    p.have("hab: !x. In x a ==> In x b").by_unfold("h1", SUBSET_DEF)
    p.have("hba: !x. In x b ==> In x a").by_unfold("h2", SUBSET_DEF)
    p.have("ext: !x. In x a = In x b").by(GEN_IFF, "hab", "hba")
    p.thus("a = b").by_match(EXTENSIONALITY, "ext")


if __name__ == "__main__":
    for label, th in [
        ("SUBSET_DEF", SUBSET_DEF),
        ("TRANS_DEF", TRANS_DEF),
        ("EQUINUM_DEF", EQUINUM_DEF),
        ("EXTENSIONALITY", EXTENSIONALITY),
        ("FOUNDATION", FOUNDATION),
        ("PAIRING", PAIRING),
        ("UNION", UNION),
        ("POWERSET", POWERSET),
        ("REPLACEMENT", REPLACEMENT),
        ("INFINITY", INFINITY),
        ("TARSKI_A", TARSKI_A),
        ("CLASS_AC", CLASS_AC),
        ("SUBSET_ANTISYM", SUBSET_ANTISYM),
    ]:
        print(f"{label}: {pp_thm(th)}")
