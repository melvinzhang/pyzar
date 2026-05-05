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
    mk_type, new_type, new_constant, new_axiom,
    ASSUME, EQ_MP, DEDUCT_ANTISYM_RULE,
)
from basics import mk_const
from parser import (
    add_const, add_type, set_default_var_ty, parse, parse_type, define, pp_thm,
)
import axioms  # noqa: F401 -- registers !, ?, /\, \/, ==>, ~, @, =, T, F
from tactics import (
    SPEC, GEN, DISCH, MP, AP_TERM, AP_THM, SYM,
    CONJ, CONJUNCT1, CONJUNCT2, UNFOLD,
    DISJ1, DISJ_CASES, REFL,
)
from basics import dest_eq, rand
from axioms import dest_imp, dest_forall, dest_disj, dest_exists, dest_neg
from classical import NOT_EX_TO_FORALL_NOT
from proof import proof


# ---------------------------------------------------------------------------
# Base type V and membership In
# ---------------------------------------------------------------------------

new_type("V", 0)
V = mk_type("V", [])
add_type("V", V)
set_default_var_ty(V)

new_constant("In", parse_type("V -> V -> bool"))
In = mk_const("In", [])
add_const("In", In)

# Class functions V -> V are heavy use; expose the type as a parser alias
# so axiom bodies can write ``?f:VV. ...``.
VV = parse_type("V -> V")


# ---------------------------------------------------------------------------
# Subset, transitive set, equinumerosity (size comparison via class function)
# ---------------------------------------------------------------------------

# Subset s t  <=>  every element of s is an element of t.
SUBSET_DEF = define(
    "Subset", "V -> V -> bool",
    "\\s t. !x. In x s ==> In x t")

# Trans u  <=>  every member of u is also a subset of u (transitive set).
TRANS_DEF = define(
    "Trans", "V -> bool",
    "\\u. !x. In x u ==> Subset x u")

# Equinum a b  <=>  there is a class function f : V -> V whose restriction
# to a is a bijection onto b. Standard HOL-ZF encoding -- f is a
# meta-level function, not an internal set-theoretic graph.
EQUINUM_DEF = define(
    "Equinum", "V -> V -> bool",
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
RR = parse_type("V -> V -> bool")
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

def IFF_AT(th_pq, th_qp):
    """``|- p ==> q``, ``|- q ==> p``  =>  ``|- p = q``.

    Iff-intro at a single point. Uses ``DEDUCT_ANTISYM_RULE`` after crossing
    the two implications under ASSUMEd antecedents."""
    p_t, _ = dest_imp(th_pq._concl)
    q_t, _ = dest_imp(th_qp._concl)
    th_q = MP(th_pq, ASSUME(p_t))
    th_p = MP(th_qp, ASSUME(q_t))
    return SYM(DEDUCT_ANTISYM_RULE(th_q, th_p))


def GEN_IFF(th_fab, th_fba):
    """``|- !x. P x ==> Q x``, ``|- !x. Q x ==> P x``  =>  ``|- !x. P x = Q x``.

    Pointwise iff-intro under a leading universal."""
    pred = dest_forall(th_fab._concl)
    x = pred.bvar
    return GEN(x, IFF_AT(SPEC(x, th_fab), SPEC(x, th_fba)))


@proof
def SUBSET_ANTISYM(p):
    p.goal("!a b. Subset a b /\\ Subset b a ==> a = b")
    p.fix("a b")
    p.assume("(h1, h2): Subset a b /\\ Subset b a")
    p.have("hab: !x. In x a ==> In x b").by_unfold("h1", SUBSET_DEF)
    p.have("hba: !x. In x b ==> In x a").by_unfold("h2", SUBSET_DEF)
    p.have("ext: !x. In x a = In x b").by(GEN_IFF, "hab", "hba")
    p.thus("a = b").by_match(EXTENSIONALITY, "ext")


# ---------------------------------------------------------------------------
# No set is its own member.
#
# Classic ZF theorem: ``!x. ~In x x``. Proof (Foundation + Pairing): assume
# In x x. PAIRING(x, x) gives the singleton {x}. Apply FOUNDATION to {x};
# the unique disjoint element must be x itself, but In x x and In x in {x}
# witness non-disjointness -- contradiction.
#
# This is the first theorem in the file that actually uses both PAIRING and
# FOUNDATION. NO_UNIVERSAL ("there is no universal set") follows as a
# one-line corollary: a universal U would satisfy In U U, contradicting
# this theorem.
# ---------------------------------------------------------------------------

def IN_SINGLETON(sing_eq):
    """``|- !w. In w s = (w = a \\/ w = a)``  =>  ``|- In a s``.

    The pairing-given equation for the singleton ``{a}``, instantiated at
    ``a`` itself: ``a = a \\/ a = a`` is true by REFL, so the pulled-back
    membership is too. The body's left disjunct supplies ``a`` directly,
    so the helper carries no extra args."""
    pred = dest_forall(sing_eq._concl)
    _, rhs_body = dest_eq(pred.body)
    left_eq, _ = dest_disj(rhs_body)
    _, a_t = dest_eq(left_eq)
    spec = SPEC(a_t, sing_eq)                         # |- In a s = (a = a \/ a = a)
    _, right_disj = dest_disj(rand(spec._concl))
    or_th = DISJ1(REFL(a_t), right_disj)              # |- a = a \/ a = a
    return EQ_MP(SYM(spec), or_th)


def OR_REFL_ELIM(or_th):
    """``|- p \\/ p``  =>  ``|- p``. Iff-of-degenerate-disjunction."""
    p_t, _ = dest_disj(or_th._concl)
    th_imp = DISCH(p_t, ASSUME(p_t))                  # |- p ==> p
    return DISJ_CASES(or_th, th_imp, th_imp)


def MEMBER_DISJ(spec_eq, in_th):
    """Combine ``|- In a s = (a = x \\/ a = x)`` and ``|- In a s`` into
    ``|- a = x`` -- specialise singleton membership to a singleton's
    canonical element."""
    return OR_REFL_ELIM(EQ_MP(spec_eq, in_th))


@proof
def NO_SELF_MEMBER(p):
    p.goal("!x. ~In x x")
    p.fix("x")
    with p.suppose("hxx: In x x"):
        # PAIRING(x, x) -- the unordered pair {x, x} = {x}.
        p.have("h_pair: ?p. !w. In w p = (w = x \\/ w = x)").by_match(PAIRING)
        p.choose("s", from_="h_pair")          # s_eq : !w. In w s = (w = x \/ w = x)
        p.have("h_xs: In x s").by(IN_SINGLETON, "s_eq")

        # FOUNDATION applied to the non-empty {x}.
        p.have("h_ne: ?z. In z s").by_witness("x", "h_xs")
        p.have("h_found: ?y. In y s /\\ ~(?z. In z s /\\ In z y)") \
            .by_match(FOUNDATION, "h_ne")
        p.choose("y", from_="h_found")         # y_eq : In y s /\ ~(?z. In z s /\ In z y)
        p.have("y_in: In y s").by(CONJUNCT1, "y_eq")
        p.have("y_disj: ~(?z. In z s /\\ In z y)").by(CONJUNCT2, "y_eq")

        # The singleton has only x as a member, so y = x.
        p.have("s_at_y: In y s = (y = x \\/ y = x)").by("s_eq", "y")
        p.have("eq_yx: y = x").by(MEMBER_DISJ, "s_at_y", "y_in")

        # Substitute y |-> x in y_disj and witness the existential at z = x.
        p.have("y_disj_x: ~(?z. In z s /\\ In z x)").by_rewrite_of("y_disj", ["eq_yx"])
        p.have("h_conj: In x s /\\ In x x").by(CONJ, "h_xs", "hxx")
        p.have("h_ex: ?z. In z s /\\ In z x").by_witness("x", "h_conj")
        p.absurd().by_conj("h_ex", "y_disj_x")


# ---------------------------------------------------------------------------
# No universal set (Russell-style corollary).
#
# A universal U would satisfy In U U, contradicting NO_SELF_MEMBER. The
# proof is one ``choose`` plus the corollary instantiation.
# ---------------------------------------------------------------------------

@proof
def NO_UNIVERSAL(p):
    p.goal("~(?u. !x. In x u)")
    with p.suppose("hu: ?u. !x. In x u"):
        p.choose("u", from_="hu")              # u_eq : !x. In x u
        p.have("h_uu: In u u").by("u_eq", "u")
        p.have("h_not: ~In u u").by(NO_SELF_MEMBER, "u")
        p.absurd().by_conj("h_uu", "h_not")


# ---------------------------------------------------------------------------
# Empty set: existence and uniqueness.
#
# Existence: INFINITY's first clause supplies a member of the inductive
# set with no members of its own -- that's our empty set.
# Uniqueness: pure EXTENSIONALITY -- two memberless sets agree on every
# membership predicate, hence are equal.
# ---------------------------------------------------------------------------

def NOT_EX_PRED(not_th):
    """``|- ~(?v. body)``  =>  ``|- !v. ~body``."""
    return NOT_EX_TO_FORALL_NOT(not_th, dest_exists(dest_neg(not_th._concl)))


@proof
def EMPTY_EXISTS(p):
    p.goal("?e. !x. ~In x e")
    p.have("h_inf: ?I. (?z. In z I /\\ ~(?w. In w z)) /\\ "
           "(!x. In x I ==> ?y. In y I /\\ (!w. In w y = (In w x \\/ w = x)))") \
        .by(INFINITY)
    p.choose("I", from_="h_inf")               # I_eq : conjunction
    p.have("h_empty_in_I: ?z. In z I /\\ ~(?w. In w z)").by(CONJUNCT1, "I_eq")
    p.choose("z", from_="h_empty_in_I")        # z_eq : In z I /\ ~(?w. In w z)
    p.have("h_no_w: ~(?w. In w z)").by(CONJUNCT2, "z_eq")
    p.have("h_forall: !x. ~In x z").by(NOT_EX_PRED, "h_no_w")
    p.thus("?e. !x. ~In x e").by_witness("z", "h_forall")


@proof
def EMPTY_UNIQUE(p):
    p.goal("!a b. (!x. ~In x a) /\\ (!x. ~In x b) ==> a = b")
    p.fix("a b")
    p.assume("(ha, hb): (!x. ~In x a) /\\ (!x. ~In x b)")
    with p.have("hext: !x. In x a = In x b").proof():
        p.fix("x")
        p.have("h_na: ~In x a").by("ha", "x")
        p.have("h_nb: ~In x b").by("hb", "x")
        # ~In x a and ~In x b both reduce to F via boolean reasoning, so
        # In x a = In x b. Use iff-intro under ASSUMEd absurd antecedents.
        with p.have("imp_ab: In x a ==> In x b").proof():
            p.assume("hxa: In x a")
            p.absurd().by_conj("hxa", "h_na")
        with p.have("imp_ba: In x b ==> In x a").proof():
            p.assume("hxb: In x b")
            p.absurd().by_conj("hxb", "h_nb")
        p.thus("In x a = In x b").by(IFF_AT, "imp_ab", "imp_ba")
    p.thus("a = b").by_match(EXTENSIONALITY, "hext")


# ---------------------------------------------------------------------------
# Name the empty set as a kernel constant Empty (= Hilbert-select on the
# empty-set existence). EMPTY_PROP exposes its characteristic property
# ``!x. ~In x Empty`` for use by downstream proofs.
# ---------------------------------------------------------------------------

EMPTY_DEF = define("Empty", V, "@e. !x. ~In x e")


@proof
def EMPTY_PROP(p):
    p.goal("!x. ~In x Empty")
    p.have("hex: ?e. !x. ~In x e").by(EMPTY_EXISTS)
    p.choose("e0: !x. ~In x e0", from_="hex")
    p.thus("!x. ~In x Empty").by_rewrite_of("e0_eq", [SYM(EMPTY_DEF)])


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
        ("NO_SELF_MEMBER", NO_SELF_MEMBER),
        ("NO_UNIVERSAL", NO_UNIVERSAL),
        ("EMPTY_EXISTS", EMPTY_EXISTS),
        ("EMPTY_UNIQUE", EMPTY_UNIQUE),
        ("EMPTY_DEF", EMPTY_DEF),
        ("EMPTY_PROP", EMPTY_PROP),
    ]:
        print(f"{label}: {pp_thm(th)}")
