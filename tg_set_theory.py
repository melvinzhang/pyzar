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
    mk_type,
    new_type,
    new_constant,
    new_axiom,
    ASSUME,
    EQ_MP,
    INST,
    TRANS,
    DEDUCT_ANTISYM_RULE,
)
from basics import mk_const
from parser import (
    add_const,
    add_type,
    set_default_var_ty,
    parse,
    parse_type,
    define,
    pp_thm,
)
import axioms  # noqa: F401 -- registers !, ?, /\, \/, ==>, ~, @, =, T, F
from tactics import (
    SPEC,
    GEN,
    DISCH,
    MP,
    AP_TERM,
    AP_THM,
    SYM,
    CONJ,
    CONJUNCT1,
    CONJUNCT2,
    UNFOLD,
    DISJ1,
    DISJ_CASES,
    REFL,
    BETA_RULE,
)
from basics import dest_eq, rand
from axioms import dest_imp, dest_forall, dest_disj, dest_exists, dest_neg
from classical import NOT_EX_TO_FORALL_NOT, EXCLUDED_MIDDLE
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
SUBSET_DEF = define("Subset", "V -> V -> bool", "\\s t. !x. In x s ==> In x t")

# Trans u  <=>  every member of u is also a subset of u (transitive set).
TRANS_DEF = define("Trans", "V -> bool", "\\u. !x. In x u ==> Subset x u")

# Equinum a b  <=>  there is a class function f : V -> V whose restriction
# to a is a bijection onto b. Standard HOL-ZF encoding -- f is a
# meta-level function, not an internal set-theoretic graph.
EQUINUM_DEF = define(
    "Equinum",
    "V -> V -> bool",
    parse(
        "\\a b. ?f:VV. "
        "(!x. In x a ==> In (f x) b) /\\ "
        "(!x y. In x a /\\ In y a /\\ f x = f y ==> x = y) /\\ "
        "(!y. In y b ==> ?x. In x a /\\ f x = y)",
        VV=VV,
    ),
)


# ---------------------------------------------------------------------------
# ZF axioms
# ---------------------------------------------------------------------------

# Extensionality: sets with the same members are equal.
EXTENSIONALITY = new_axiom(parse("!a b. (!x. In x a = In x b) ==> a = b"))

# Foundation: every nonempty set has an element disjoint from it.
FOUNDATION = new_axiom(
    parse("!a. (?x. In x a) ==> (?x. In x a /\\ ~(?y. In y a /\\ In y x))")
)

# Pairing: for any two sets there is a set whose members are exactly them.
PAIRING = new_axiom(parse("!a b. ?p. !x. In x p = (x = a \\/ x = b)"))

# Union: for any set a, the union of its members exists as a set.
UNION = new_axiom(parse("!a. ?u. !x. In x u = (?y. In x y /\\ In y a)"))

# Powerset: for any set a, the set of subsets of a exists.
POWERSET = new_axiom(parse("!a. ?p. !x. In x p = Subset x a"))

# Replacement: if R is functional on a, then the R-image of a is a set.
# Functionality is the explicit "at most one image" condition; we don't
# need a unique-existential constant.
RR = parse_type("V -> V -> bool")
REPLACEMENT = new_axiom(
    parse(
        "!a. (!x y1 y2. In x a /\\ R x y1 /\\ R x y2 ==> y1 = y2) ==> "
        "(?b. !y. In y b = (?x. In x a /\\ R x y))",
        R=RR,
    )
)

# Infinity: an inductive set exists -- it contains an empty set and is
# closed under x |-> x u {x}. Stated unfolded so we don't yet need
# constants for empty / successor.
INFINITY = new_axiom(
    parse(
        "?I. (?z. In z I /\\ ~(?w. In w z)) /\\ "
        "(!x. In x I ==> (?y. In y I /\\ (!w. In w y = (In w x \\/ w = x))))"
    )
)


# ---------------------------------------------------------------------------
# Tarski's Axiom A (Bourbaki/Grothendieck form): every set is contained in
# a Grothendieck universe.
#
# A universe U satisfies:
#   (1) Trans U                    -- members are subsets
#   (2) pair-closure               -- a, b in U ==> {a, b} in U
#   (3) powerset-closure           -- y in U ==> Pow y in U
#   (4) indexed-union closure      -- Fam in U ==> Union Fam in U
#
# This is the modern (Bourbaki SGA 4 / mathlib ``IsGrothendieckUniverse``)
# formulation. Equivalent to Tarski's 1938 size-reflection form in
# ZFC-with-ordinals, but here we take the closure clauses directly --
# without ordinal apparatus the equivalence is one-way (size-reflection
# alone cannot derive union-closure; we'd need Hartogs/cofinality).
#
# Iterating gives a proper class of inaccessibles. Choice follows (every
# set lives in a universe whose ordinal structure well-orders it), so it
# is not posted separately. ZF + A = TG.
# ---------------------------------------------------------------------------

TARSKI_A = new_axiom(
    parse(
        "!x. ?u. In x u /\\ Trans u /\\ "
        "(!a b. In a u /\\ In b u ==> "
        "(?p. In p u /\\ (!w. In w p = (w = a \\/ w = b)))) /\\ "
        "(!y. In y u ==> (?p. In p u /\\ (!z. In z p = Subset z y))) /\\ "
        "(!Fam. In Fam u ==> "
        "(?B. In B u /\\ (!w. In w B = (?z. In z Fam /\\ In w z))))"
    )
)


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
    eq = UNFOLD(CHOOSE_DEF, x_t)  # |- Choose x = @y. In y x
    lift = AP_THM(AP_TERM(In, eq), x_t)  # |- In (Choose x) x = In (@y. In y x) x
    return EQ_MP(SYM(lift), y0_eq)


@proof
def CLASS_AC(p):
    p.goal(
        "!X. (!x. In x X ==> ?y. In y x) ==> (?f:VV. !x. In x X ==> In (f x) x)",
        types={"VV": VV},
    )
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
    spec = SPEC(a_t, sing_eq)  # |- In a s = (a = a \/ a = a)
    _, right_disj = dest_disj(rand(spec._concl))
    or_th = DISJ1(REFL(a_t), right_disj)  # |- a = a \/ a = a
    return EQ_MP(SYM(spec), or_th)


def OR_REFL_ELIM(or_th):
    """``|- p \\/ p``  =>  ``|- p``. Iff-of-degenerate-disjunction."""
    p_t, _ = dest_disj(or_th._concl)
    th_imp = DISCH(p_t, ASSUME(p_t))  # |- p ==> p
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
        p.choose("s", from_="h_pair")  # s_eq : !w. In w s = (w = x \/ w = x)
        p.have("h_xs: In x s").by(IN_SINGLETON, "s_eq")

        # FOUNDATION applied to the non-empty {x}.
        p.have("h_ne: ?z. In z s").by_witness("x", "h_xs")
        p.have("h_found: ?y. In y s /\\ ~(?z. In z s /\\ In z y)").by_match(
            FOUNDATION, "h_ne"
        )
        p.choose("y", from_="h_found")  # y_eq : In y s /\ ~(?z. In z s /\ In z y)
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
        p.choose("u", from_="hu")  # u_eq : !x. In x u
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
    p.have(
        "h_inf: ?I. (?z. In z I /\\ ~(?w. In w z)) /\\ "
        "(!x. In x I ==> ?y. In y I /\\ (!w. In w y = (In w x \\/ w = x)))"
    ).by(INFINITY)
    p.choose("I", from_="h_inf")  # I_eq : conjunction
    p.have("h_empty_in_I: ?z. In z I /\\ ~(?w. In w z)").by(CONJUNCT1, "I_eq")
    p.choose("z", from_="h_empty_in_I")  # z_eq : In z I /\ ~(?w. In w z)
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
        p.thus("In x a = In x b").by_iff("imp_ab", "imp_ba")
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


# ---------------------------------------------------------------------------
# A Grothendieck universe containing an inductive set -- i.e. existence
# of a strongly inaccessible cardinal.
#
# Packages the four Bourbaki-Grothendieck closure clauses plus an
# infinite-set witness as a single existential:
#
#   (inf)   the universe contains an inductive ``I`` (from INFINITY) -- so
#           its rank is past omega, ruling out the V_omega universe and
#           forcing strong inaccessibility;
#   (1)     Trans u;
#   (2)     pair-closure;
#   (3)     powerset-closure -- the strong-limit clause;
#   (4)     indexed-union closure -- the regularity / cofinality clause.
#
# The closure clauses alone admit ``V_0 = {}``, ``V_omega = HF``, and
# ``V_kappa`` for kappa strongly inaccessible. Pairing ``TARSKI_A`` with
# ``INFINITY`` rules out the first two -- ``In I u`` cannot hold for any
# countable ``u``. The proof is a straight repackaging: INFINITY yields
# ``I``, TARSKI_A applied at ``I`` yields ``u``, and CONJ glues.
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Powerset constant Pow and its characteristic property.
#
# POWERSET only asserts existence; pin a specific witness as a kernel
# constant so downstream proofs can write ``Pow x`` rather than carry an
# existential around. ``by_select_def`` extracts the body's property.
# ---------------------------------------------------------------------------

POW_DEF = define("Pow", VV, "\\x. @p. !z. In z p = Subset z x")


@proof
def POW_PROP(p):
    p.goal("!x z. In z (Pow x) = Subset z x")
    p.fix("x")
    p.have("h_ex: ?p. !z. In z p = Subset z x").by_match(POWERSET)
    p.thus("!z. In z (Pow x) = Subset z x").by_select_def(POW_DEF, "x", from_="h_ex")


# ---------------------------------------------------------------------------
# Separation as a derived schema.
#
# REPLACEMENT is stated with a free relation ``R``. Substituting
# ``R := \u v. P u /\ v = u`` and beta-reducing turns it into:
#
#   !a. (functionality, trivially true) ==>
#       ?b. !y. In y b = (?x. In x a /\ P x /\ y = x)
#
# After dispatching the trivial functionality, we get a separation schema
# parametrised by the free predicate ``P``. The body's RHS is the "raw"
# form -- the inner ``y = x`` is left in place rather than collapsed to
# the cleaner ``In y a /\ P y``, because downstream uses (Cantor) prefer
# to unfold that existential by hand at the call site.
# ---------------------------------------------------------------------------

_P_TY = parse_type("V -> bool")
_R_VAR = parse("R", R=parse_type("V -> V -> bool"))
_SEP_LAM = parse("\\u v. P u /\\ v = u", P=_P_TY)
REPLACEMENT_SEP = BETA_RULE(INST([(_SEP_LAM, _R_VAR)], REPLACEMENT))


@proof
def SEPARATION(p):
    p.goal(
        "!a. ?b. !y. In y b = (?x. In x a /\\ P x /\\ y = x)",
        types={"P": _P_TY},
    )
    p.fix("a")
    with p.have(
        "h_func: !x y1 y2. In x a /\\ (P x /\\ y1 = x) /\\ (P x /\\ y2 = x) ==> y1 = y2"
    ).proof():
        p.fix("x y1 y2")
        p.assume("h: In x a /\\ (P x /\\ y1 = x) /\\ (P x /\\ y2 = x)")
        p.have("h12: (P x /\\ y1 = x) /\\ (P x /\\ y2 = x)").by(CONJUNCT2, "h")
        p.have("h1: P x /\\ y1 = x").by(CONJUNCT1, "h12")
        p.have("h2: P x /\\ y2 = x").by(CONJUNCT2, "h12")
        p.have("h_y1x: y1 = x").by(CONJUNCT2, "h1")
        p.have("h_y2x: y2 = x").by(CONJUNCT2, "h2")
        p.thus("y1 = y2").by_thm(TRANS(p.fact("h_y1x"), SYM(p.fact("h_y2x"))))
    p.thus("?b. !y. In y b = (?u. In u a /\\ P u /\\ y = u)").by_match(
        REPLACEMENT_SEP, "h_func"
    )


# ---------------------------------------------------------------------------
# Cantor's theorem.
#
# CANTOR_NO_SURJ is the diagonal argument's actual content: no class
# function f surjects x onto Pow x. We build the diagonal
# ``D = {y in x : ~In y (f y)}`` via SEPARATION; ``D`` is a subset of
# ``x``, hence in ``Pow x``, hence has some ``d in x`` with ``f d = D``.
# Excluded middle on ``In d D`` forces a contradiction either way: if
# ``In d D`` then ``d`` witnesses the existential defining ``D``, so
# ``~In d (f d) = ~In d D``; if ``~In d D`` then ``d`` itself satisfies
# ``In d x /\ ~In d (f d) /\ d = d``, witnessing the existential and
# forcing ``In d D``.
#
# CANTOR -- the more familiar ``~Equinum x (Pow x)`` -- is then a
# corollary: an Equinum bijection includes a surjection.
# ---------------------------------------------------------------------------


@proof
def CANTOR_NO_SURJ(p):
    p.goal(
        "!x. !f:VV. ~(!w. In w (Pow x) ==> ?u. In u x /\\ f u = w)",
        types={"VV": VV},
    )
    p.fix("x")
    p.fix("f")
    with p.suppose("h_surj: !w. In w (Pow x) ==> ?u. In u x /\\ f u = w"):
        # Build D = {y in x : ~In y (f y)} via SEPARATION at \y. ~In y (f y).
        diag_lam = p._parse("\\y. ~In y (f y)")
        P_var = parse("P", P=_P_TY)
        x_t = p._parse("x")
        sep_at_diag = BETA_RULE(INST([(diag_lam, P_var)], SPEC(x_t, SEPARATION)))
        p.have("h_sep: ?b. !y. In y b = (?u. In u x /\\ ~In u (f u) /\\ y = u)").by_thm(
            sep_at_diag
        )
        p.choose("D", from_="h_sep")

        # Subset D x.
        with p.have("h_Dsub: Subset D x").proof():
            with p.have("h_pt: !y. In y D ==> In y x").proof():
                p.fix("y")
                p.assume("h_yD: In y D")
                p.have("h_yD_ex: ?u. In u x /\\ ~In u (f u) /\\ y = u").by_eq_mp(
                    SPEC(p._parse("y"), p.fact("D_eq")), "h_yD"
                )
                p.choose("u", from_="h_yD_ex")
                p.have("h_ux: In u x").by(CONJUNCT1, "u_eq")
                p.have("h_yu_rest: ~In u (f u) /\\ y = u").by(CONJUNCT2, "u_eq")
                p.have("h_yu: y = u").by(CONJUNCT2, "h_yu_rest")
                p.thus("In y x").by_rewrite_of("h_ux", [SYM(p.fact("h_yu"))])
            p.thus("Subset D x").by_unfold("h_pt", SUBSET_DEF)

        # In D (Pow x).
        p.have("h_DPow: In D (Pow x)").by_eq_mp(
            SYM(SPEC(p._parse("D"), SPEC(p._parse("x"), POW_PROP))),
            "h_Dsub",
        )

        # Surjectivity gives d in x with f d = D.
        p.have("h_surj_D: In D (Pow x) ==> ?u. In u x /\\ f u = D").by_inst(
            "h_surj", "D"
        )
        p.have("h_d_ex: ?u. In u x /\\ f u = D").by_thm(
            MP(p.fact("h_surj_D"), p.fact("h_DPow"))
        )
        p.choose("d", from_="h_d_ex")
        p.have("h_dx: In d x").by(CONJUNCT1, "d_eq")
        p.have("h_fdD: f d = D").by(CONJUNCT2, "d_eq")

        # Diagonal contradiction.
        with p.cases_on(EXCLUDED_MIDDLE, "In d D"):
            with p.case("h_inD: In d D"):
                p.have("h_dD_ex: ?u. In u x /\\ ~In u (f u) /\\ d = u").by_eq_mp(
                    SPEC(p._parse("d"), p.fact("D_eq")), "h_inD"
                )
                p.choose("u", from_="h_dD_ex")
                p.have("h_rest1: ~In u (f u) /\\ d = u").by(CONJUNCT2, "u_eq")
                p.have("h_nfu: ~In u (f u)").by(CONJUNCT1, "h_rest1")
                p.have("h_du: d = u").by(CONJUNCT2, "h_rest1")
                p.have("h_nfd: ~In d (f d)").by_rewrite_of(
                    "h_nfu", [SYM(p.fact("h_du"))]
                )
                p.have("h_inFd: In d (f d)").by_rewrite_of(
                    "h_inD", [SYM(p.fact("h_fdD"))]
                )
                p.absurd().by_conj("h_inFd", "h_nfd")
            with p.case("h_notinD: ~In d D"):
                p.have("h_nfd: ~In d (f d)").by_rewrite_of(
                    "h_notinD", [p.fact("h_fdD")]
                )
                p.have("h_inner: In d x /\\ ~In d (f d) /\\ d = d").by(
                    CONJ,
                    "h_dx",
                    CONJ(p.fact("h_nfd"), REFL(p._parse("d"))),
                )
                p.have("h_dD_ex: ?u. In u x /\\ ~In u (f u) /\\ d = u").by_witness(
                    "d", "h_inner"
                )
                p.have("h_inD: In d D").by_eq_mp(
                    SYM(SPEC(p._parse("d"), p.fact("D_eq"))), "h_dD_ex"
                )
                p.absurd().by_conj("h_inD", "h_notinD")


@proof
def CANTOR(p):
    p.goal("!x. ~Equinum x (Pow x)", types={"VV": VV})
    p.fix("x")
    with p.suppose("h_eq: Equinum x (Pow x)"):
        p.have(
            "h_body: ?f:VV. (!u. In u x ==> In (f u) (Pow x)) /\\ "
            "(!u v. In u x /\\ In v x /\\ f u = f v ==> u = v) /\\ "
            "(!w. In w (Pow x) ==> ?u. In u x /\\ f u = w)"
        ).by_unfold("h_eq", EQUINUM_DEF)
        p.choose("f", from_="h_body")
        p.have(
            "h_rest: (!u v. In u x /\\ In v x /\\ f u = f v ==> u = v) /\\ "
            "(!w. In w (Pow x) ==> ?u. In u x /\\ f u = w)"
        ).by(CONJUNCT2, "f_eq")
        p.have("h_surj: !w. In w (Pow x) ==> ?u. In u x /\\ f u = w").by(
            CONJUNCT2, "h_rest"
        )
        p.have("h_no: ~(!w. In w (Pow x) ==> ?u. In u x /\\ f u = w)").by_inst(
            CANTOR_NO_SURJ, "x", "f"
        )
        p.absurd().by_conj("h_surj", "h_no")


# ---------------------------------------------------------------------------
# SMALL_MEMBER -- members of a Grothendieck universe are smaller than the
# universe.
#
# If ``In x u``, ``Trans u``, and ``u`` is closed under powerset (clause 3
# of TARSKI_A), then ``~Equinum x u``. From a hypothetical bijection
# ``f : x <-> u`` we build a surjection ``x -> Pow x`` and contradict
# CANTOR_NO_SURJ. The surjection works because ``Pow x in u`` (powerset
# clause + extensional match against POW_PROP), then ``Subset (Pow x) u``
# (Trans), so any ``w in Pow x`` is also in ``u`` and lies in the image
# of ``f``.
# ---------------------------------------------------------------------------


@proof
def SMALL_MEMBER(p):
    p.goal(
        "!x u. In x u /\\ Trans u /\\ "
        "(!y. In y u ==> ?p. In p u /\\ (!z. In z p = Subset z y)) ==> "
        "~Equinum x u",
        types={"VV": VV},
    )
    p.fix("x u")
    p.assume(
        "(h_xu, h_trans, h_pow): In x u /\\ Trans u /\\ "
        "(!y. In y u ==> ?p. In p u /\\ (!z. In z p = Subset z y))"
    )
    with p.suppose("h_eq: Equinum x u"):
        # 1. Get a u-internal "powerset of x" and identify it with Pow x.
        p.have(
            "h_pow_at_x: In x u ==> ?p. In p u /\\ (!z. In z p = Subset z x)"
        ).by_inst("h_pow", "x")
        p.have("h_pow_ex: ?p. In p u /\\ (!z. In z p = Subset z x)").by_thm(
            MP(p.fact("h_pow_at_x"), p.fact("h_xu"))
        )
        p.choose("p", from_="h_pow_ex")
        p.have("h_pu: In p u").by(CONJUNCT1, "p_eq")
        p.have("h_p_def: !z. In z p = Subset z x").by(CONJUNCT2, "p_eq")
        with p.have("h_p_eq_Pow: p = Pow x").proof():
            with p.have("h_ext: !z. In z p = In z (Pow x)").proof():
                p.fix("z")
                p.have("h_pz: In z p = Subset z x").by_inst("h_p_def", "z")
                p.have("h_Powz: In z (Pow x) = Subset z x").by_inst(POW_PROP, "x", "z")
                p.thus("In z p = In z (Pow x)").by_thm(
                    TRANS(p.fact("h_pz"), SYM(p.fact("h_Powz")))
                )
            p.thus("p = Pow x").by_match(EXTENSIONALITY, "h_ext")
        p.have("h_PowU: In (Pow x) u").by_rewrite_of("h_pu", [p.fact("h_p_eq_Pow")])
        # 2. Subset (Pow x) u from Trans u + In (Pow x) u.
        p.have("h_trans_unf: !y. In y u ==> Subset y u").by_unfold("h_trans", TRANS_DEF)
        p.have("h_PowU_imp: In (Pow x) u ==> Subset (Pow x) u").by_inst(
            "h_trans_unf", "Pow x"
        )
        p.have("h_PowSub: Subset (Pow x) u").by_thm(
            MP(p.fact("h_PowU_imp"), p.fact("h_PowU"))
        )
        p.have("h_PSU_unf: !z. In z (Pow x) ==> In z u").by_unfold(
            "h_PowSub", SUBSET_DEF
        )
        # 3. Unfold Equinum: get f and its surjectivity onto u.
        p.have(
            "h_body: ?f:VV. (!y. In y x ==> In (f y) u) /\\ "
            "(!y1 y2. In y1 x /\\ In y2 x /\\ f y1 = f y2 ==> y1 = y2) /\\ "
            "(!w. In w u ==> ?y. In y x /\\ f y = w)"
        ).by_unfold("h_eq", EQUINUM_DEF)
        p.choose("f", from_="h_body")
        p.have(
            "h_rest: (!y1 y2. In y1 x /\\ In y2 x /\\ f y1 = f y2 ==> y1 = y2) /\\ "
            "(!w. In w u ==> ?y. In y x /\\ f y = w)"
        ).by(CONJUNCT2, "f_eq")
        p.have("h_surj_u: !w. In w u ==> ?y. In y x /\\ f y = w").by(
            CONJUNCT2, "h_rest"
        )
        # 4. Build the surjection x -> Pow x.
        with p.have("h_surj_Pow: !w. In w (Pow x) ==> ?y. In y x /\\ f y = w").proof():
            p.fix("w")
            p.assume("h_wPow: In w (Pow x)")
            p.have("h_w_imp: In w (Pow x) ==> In w u").by_inst("h_PSU_unf", "w")
            p.have("h_wu: In w u").by_thm(MP(p.fact("h_w_imp"), p.fact("h_wPow")))
            p.have("h_su_imp: In w u ==> ?y. In y x /\\ f y = w").by_inst(
                "h_surj_u", "w"
            )
            p.thus("?y. In y x /\\ f y = w").by_thm(
                MP(p.fact("h_su_imp"), p.fact("h_wu"))
            )
        # 5. Contradicts CANTOR_NO_SURJ at x and f. Rename the inner bound
        # ``?u`` to ``?y`` because the outer free ``u`` would otherwise shadow.
        p.have("h_no: ~(!w. In w (Pow x) ==> ?y. In y x /\\ f y = w)").by_inst(
            CANTOR_NO_SURJ, "x", "f"
        )
        p.absurd().by_conj("h_surj_Pow", "h_no")


@proof
def INACCESSIBLE_UNIVERSE(p):
    inductive = (
        "(?z. In z I /\\ ~(?w. In w z)) /\\ "
        "(!x. In x I ==> (?y. In y I /\\ (!w. In w y = (In w x \\/ w = x))))"
    )
    rest = (
        "Trans u /\\ "
        "(!a b. In a u /\\ In b u ==> "
        "(?p. In p u /\\ (!w. In w p = (w = a \\/ w = b)))) /\\ "
        "(!y. In y u ==> (?p. In p u /\\ (!z. In z p = Subset z y))) /\\ "
        "(!Fam. In Fam u ==> "
        "(?B. In B u /\\ (!w. In w B = (?z. In z Fam /\\ In w z))))"
    )
    contains_inf = f"(?I. In I u /\\ {inductive})"
    full = f"{contains_inf} /\\ {rest}"
    p.goal(f"?u. {full}")
    # Inductive I from INFINITY.
    p.have(f"h_inf: ?I. {inductive}").by(INFINITY)
    p.choose("I", from_="h_inf")
    # Universe u containing I, from TARSKI_A.
    p.have(f"h_uni: ?u. In I u /\\ {rest}").by_match(TARSKI_A)
    p.choose("u", from_="h_uni")
    p.have("h_in: In I u").by(CONJUNCT1, "u_eq")
    p.have(f"h_rest: {rest}").by(CONJUNCT2, "u_eq")
    # Witness the inner ?I with our chosen I.
    p.have(f"h_pair: In I u /\\ {inductive}").by(CONJ, "h_in", "I_eq")
    p.have(f"h_contains_inf: {contains_inf}").by_witness("I", "h_pair")
    # Glue and witness u.
    p.have(f"h_all: {full}").by(CONJ, "h_contains_inf", "h_rest")
    p.thus(f"?u. {full}").by_witness("u", "h_all")


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
        ("POW_DEF", POW_DEF),
        ("POW_PROP", POW_PROP),
        ("SEPARATION", SEPARATION),
        ("CANTOR_NO_SURJ", CANTOR_NO_SURJ),
        ("CANTOR", CANTOR),
        ("SMALL_MEMBER", SMALL_MEMBER),
        ("INACCESSIBLE_UNIVERSE", INACCESSIBLE_UNIVERSE),
    ]:
        print(f"{label}: {pp_thm(th)}")
