"""Goedel's first incompleteness theorem, formalised over ``hf_sets.py``.

SKETCH ONLY -- this file lays out the construction; the proofs are
stubbed with strategy comments rather than executed. The goal is to
state and prove, as a HOL theorem, that the formalised first-order
theory Q (Robinson arithmetic) is incomplete: there is an explicit
sentence ``G_Q`` such that

    |- ~ Q_proves G_Q  /\\  ~ Q_proves (Not G_Q).

The whole development lives over ``hf_sets.py`` plus ``nat.py``.
Axiomatic cost: zero. HOL + HF already proves the consistency of Q
(Q has a model -- the von Neumann numerals inside HF) so the
incompleteness statement is *unconditional*, not "if Q is consistent".

------------------------------------------------------------------
Why Q rather than PA
------------------------------------------------------------------

Robinson's Q is the cheapest theory the incompleteness proof goes
through. Its seven closed axioms are PA's recursion equations plus a
"non-zero has a predecessor" clause, and *no* induction schema:

    Q1.  ~(S x = 0)
    Q2.  S x = S y  ==>  x = y
    Q3.  ~(x = 0)  ==>  ?y. x = S y          (predecessor)
    Q4.  x + 0 = x
    Q5.  x + S y = S (x + y)
    Q6.  x * 0 = 0
    Q7.  x * S y = x * y + x

Q is *strikingly weak*: it does not prove ``x + y = y + x``, nor
``!x. x = 0 \\/ ?y. x = S y`` (only its numeral instances). What it
*does* prove is enough: every primitive recursive predicate is
representable in Q (Goedel-Bernays beta function trick), which is the
sole hypothesis needed for the diagonal lemma. So Q is essentially
undecidable, and the same holds for every consistent extension --
including PA, ZFC, and HOL itself.

The headline theorem reads identically for Q and PA. The implementation
is significantly cheaper for Q: the induction schema is an infinite
axiom family whose encoding-as-a-decidable-predicate is ~150 lines of
substitution bookkeeping that we don't have to write. All of pyzar's
downstream consumers want the metatheorem ("PA, ZFC, ... are
incomplete"), and that follows from incompleteness of Q by the
essential-undecidability corollary at the end of Stage 5.

------------------------------------------------------------------
The idea (Goedel 1931; modern presentations: Smullyan, Boolos)
------------------------------------------------------------------

Three ingredients:

  (1) *Arithmetization.* Encode each Q term, formula, and proof as a
      hereditarily finite set, hence as a natural number. With ``HF``
      this is a one-liner: terms and formulas are finite trees, which
      are HF sets, which are nums. Goedel numbering is the Ackermann
      encoding of ``hf_sets.py``, applied to whatever inductive grammar
      we pick for syntax.

  (2) *Representation.* Define the primitive recursive predicate
      ``Proof_Q(p, n)`` -- "the HF-encoded proof ``p`` is a Q
      derivation of the formula with HF-encoding ``n``" -- as a HOL
      predicate on ``num``. Define
            Prov_Q(n)  :<=>  ?p. Proof_Q(p, n).
      Both ``Proof_Q`` and ``Prov_Q`` are *HOL* predicates; they are
      not at this stage statements *inside* Q.

  (3) *Diagonal lemma.* For every Q formula ``phi(x)`` with one free
      variable there is a sentence ``psi`` such that
            Q |- psi <==> phi(numeral_of(godelnum psi)).
      Apply with ``phi(x) := Not (Prov_Q_internal x)`` to get the
      Goedel sentence ``G_Q``:
            Q |- G_Q <==> Not (Prov_Q_internal (numeral_of (godelnum G_Q))).

The "internal" provability predicate ``Prov_Q_internal`` is the Q
formula expressing what ``Prov_Q`` (the HOL predicate) computes -- the
*representability* theorem says these two coincide on standard inputs:

    |- !n. Prov_Q n  <==>  Q |- Prov_Q_internal (numeral_of n).

With those two pieces, incompleteness is short:

    Q |- G_Q   ==>   Prov_Q (godelnum G_Q)              (definitions)
              ==>    Q |- Prov_Q_internal (numeral_of ...)  (representability)
              ==>    Q |- Not G_Q                       (diagonal)
              ==>    Q inconsistent                     (combine)

    Q |- Not G_Q   ==>  Q |- Prov_Q_internal (numeral_of ...)  (diagonal)
                   ==>  Prov_Q (godelnum G_Q)           (Sigma_1 soundness)
                   ==>  Q |- G_Q                        (definitions)
                   ==>  Q inconsistent                  (combine)

HOL + HF discharges the consistency hypothesis on its own (the standard
model lives inside HF), so we conclude unconditionally.

------------------------------------------------------------------
The HOL encoding hurdle
------------------------------------------------------------------

There isn't one for the data: ``hf_sets.py`` already gives us finite
trees over ``num``, so terms and formulas have natural Goedel numbers.
The work is in writing down a *concrete* proof system and a *concrete*
provability predicate -- and in proving the diagonal lemma and the
representability theorem against that concrete choice.

Two design choices:

  (a) *Hilbert-style*. Q has seven equation/inequation axioms plus the
      standard finite list of propositional, quantifier, and equality
      axioms; rules are modus ponens and generalization. Proof = list
      of formulas, each either an axiom instance or following by a
      rule from earlier lines. Easy to encode, ugly to do real proofs
      in. We use this because we never *do* real proofs in Q -- we
      only check that a few specific proofs exist.

  (b) *Natural deduction*. Cleaner proof terms; more work to encode.
      Skippable.

We take (a). ``Proof_Q(p, n)`` becomes a primitive recursive predicate
on ``num x num`` -- decidable, hence representable in Q by a Sigma_1
formula. That representability is the only nontrivial arithmetization
theorem in the file.

(There is no "Sigma_1-soundness axiom" to post: HOL + HF proves
Sigma_1 soundness of Q outright, since HF *is* the standard model.)
"""

# Stage 1: see q_syntax.py
# Stage 2: see q_proof.py
# Stage 3: see q_repr.py

# ---------------------------------------------------------------------------
# Stage 4 -- the diagonal lemma.
# ---------------------------------------------------------------------------
#
# Lemma (Goedel-Carnap). For every Q formula phi(x) with x as its only
# free variable there is a sentence psi such that
#
#     |- Prov_Q (godelnum (Iff psi (phi (numeral (godelnum psi))))).
#
# Proof sketch:
#   * Define the "diagonal substitution" function
#         diag(n) := godelnum (substitute(x, numeral n, formula coded by n)).
#     This is primitive recursive on godelnums; let D(x, y) represent it.
#   * Let theta(x) := ?y. D(x, y) /\\ phi(y).
#   * Let m := godelnum theta.
#   * Take psi := substitute(x, numeral m, theta) = "?y. D(numeral m, y) /\\ phi(y)".
#   * By representability of diag, Q proves D(numeral m, numeral k) iff
#     k = diag(m) = godelnum psi.
#   * Hence Q proves psi <==> phi(numeral (godelnum psi)).
#
# The proof is ~80 lines once Stage 3 is in place; it is the
# *self-application* trick written out arithmetically. Nothing in it
# uses induction, so the lemma is exactly as cheap for Q as for PA.

# ---------------------------------------------------------------------------
# Stage 5 -- the Goedel sentence and the main theorem.
# ---------------------------------------------------------------------------
#
# defn:  G_Q  :=  the diagonal-fixed-point of (Not (Prov_Q_internal x)).
#
# Equivalently:  |- Prov_Q (godelnum (Iff G_Q (Not (Prov_Q_internal (numeral (godelnum G_Q)))))).
#
# Theorem (First Incompleteness, semantic form):
#
#   |-  ~ Prov_Q (godelnum G_Q)  /\\  ~ Prov_Q (godelnum (Not G_Q))
#
# Proof:
#
#   First conjunct (Q does not prove G_Q):
#     Suppose Prov_Q (godelnum G_Q).
#     By representability,
#         Prov_Q (godelnum (Prov_Q_internal (numeral (godelnum G_Q)))).
#     By the diagonal equivalence applied internally,
#         Prov_Q (godelnum (Not G_Q)).
#     Combined with the assumption, Q proves both G_Q and ~G_Q;
#     therefore Q is inconsistent. But Q has a model in HF
#     (Stage 6), so Q is consistent -- contradiction.
#
#   Second conjunct (Q does not prove Not G_Q):
#     Suppose Prov_Q (godelnum (Not G_Q)).
#     By the diagonal equivalence,
#         Prov_Q (godelnum (Prov_Q_internal (numeral (godelnum G_Q)))).
#     The internal-provability formula is Sigma_1, and Q is Sigma_1-
#     sound (Stage 6), so the *external* Prov_Q (godelnum G_Q) holds
#     in HOL.
#     Combined with the assumption, Q proves both G_Q and ~G_Q;
#     contradiction with consistency.
#
# Corollary (Essential undecidability). Any consistent first-order
# theory T in the language of arithmetic that *extends* Q is
# incomplete. Proof: every Q-axiom is a T-theorem by hypothesis, so
# Prov_Q n ==> Prov_T n; the same G_Q (or its T-internal analogue)
# witnesses incompleteness. ~50 lines on top of Stage 5. This is how
# PA, ZFC, and HOL itself inherit incompleteness for free -- we never
# need to repeat the construction with their own provability
# predicates.
#
# The whole argument is ~150 lines once Stages 3-4 are done.

# ---------------------------------------------------------------------------
# Stage 6 -- where the consistency assumption goes.
# ---------------------------------------------------------------------------
#
# Two facts are needed but never posted as axioms:
#
#   (A)  Consistency: ~ Prov_Q (godelnum (Eq Zero (Succ Zero))).
#        Proof: HF supplies a model. The von Neumann numerals
#               0_HF := Empty,  S_HF n := union (pair n (pair n n))
#        satisfy each of Q1-Q7 -- one HOL theorem per axiom, mostly
#        one-liners (Q1 from EMPTY_PROP, Q2 from successor injectivity,
#        Q3 by case-split on Empty vs. inhabited, Q4-Q7 by unfolding
#        the HF definitions of + and * on von Neumann numerals).
#        Soundness of the proof system then transfers any HOL-witnessed
#        inconsistency of Q to an inconsistency of HF, but HF is
#        consistent (by exhibiting actual numbers). So Q is consistent.
#        ~120 lines: model construction + one line per Q axiom.
#
#        (Compare PA: each induction-schema instance is a separate
#        soundness obligation, discharged uniformly via well-ordering
#        of ``num``; ~30 extra lines.)
#
#   (B)  Sigma_1-soundness: !F. F is a Sigma_1 sentence /\\ Prov_Q F
#        ==> F holds (in HOL).
#        Proof: any Sigma_1 sentence is "?x_1 ... x_k. P(x_1, ..., x_k)"
#        with P primitive recursive. Soundness of Q's proof rules
#        transfers any Q-derivation to a HOL theorem; the HOL theorem
#        is the corresponding existential about ``num``. ~80 lines on
#        top of the soundness of propositional + first-order rules.
#
# Both (A) and (B) are HOL theorems, not posted axioms. This is the
# standard "the metatheory is stronger than Q" observation: HOL with
# HF proves Con(Q) -- in fact proves Con(PA) and Con(ZFC) too, the
# limit being TARSKI_A's inaccessibility -- so HOL knows that Q is
# incomplete.

# ---------------------------------------------------------------------------
# What this *does* and *does not* give
# ---------------------------------------------------------------------------
#
# Derived from the bare HOL kernel + ``num`` + HF (no new axioms):
#   * First incompleteness for Q: an explicit sentence G_Q, and the
#     theorem that neither G_Q nor Not G_Q is Q-provable.
#   * Essential undecidability: any consistent extension of Q in the
#     same language is incomplete. Same proof; ~50 lines on top of
#     Stage 5. This is the immediate corollary that gives
#     incompleteness for PA, ZFC, and HOL itself without any extra
#     work.
#   * Tarski's undefinability of arithmetic truth (one corollary; ~30
#     lines once the diagonal lemma is in place).
#   * Rosser's strengthening (replace Prov by the Rosser predicate;
#     the same argument yields ~ Prov_Q (godelnum R_Q) /\\
#     ~ Prov_Q (godelnum (Not R_Q)) using only consistency rather
#     than Sigma_1-soundness; ~120 lines on top of Stage 5).
#
# Not derived here:
#   * Second incompleteness ("T does not prove its own consistency")
#     for any T strong enough to support the Hilbert-Bernays-Loeb
#     derivability conditions. Q itself is *too weak* -- it cannot
#     internalise its own soundness arguments. Second incompleteness
#     starts at PA (or, more precisely, at I-Sigma_1) and requires
#     us to revisit Stage 2 with the induction schema. Cleanly
#     factored as ``godel_second.py`` against an extended substrate.
#   * Loeb's theorem and the modal logic GL: same comment as second
#     incompleteness; downstream of it.
#   * Anything inside Q proper: Q does not prove ``x + y = y + x``,
#     ``x + 0 = 0 + x``, or even ``!x. x = 0 \\/ ?y. x = Succ y``.
#     Don't try to do real arithmetic inside the formalised Q; do it
#     in HOL on ``num`` and represent the result.

# ---------------------------------------------------------------------------
# Implementation roadmap
# ---------------------------------------------------------------------------
#
# Prerequisites: ``nat.py``, ``hf_sets.py``.
#
#   1. ``q_syntax.py`` -- term and formula datatypes (as HF trees);
#      Goedel numbering; substitution; unique readability; free-
#      variable analysis. ~300 lines. (Same shape as PA's syntax
#      module; the signature is identical.)
#
#   2. ``q_proofs.py`` -- the seven Q axioms and the logical axioms
#      as predicates on godelnums; ``Proof_Q``; ``Prov_Q``; closure
#      rules. ~250 lines. (vs ~400 for PA, the saving coming from no
#      induction-schema recogniser.)
#
#   3. ``q_repr.py`` -- representability of primitive recursive
#      predicates, specialised to ``Proof_Q``, ``substitute``, and the
#      diagonal function, via the Goedel-Bernays beta function. Yields
#      ``Prov_Q_internal`` and the representability theorem. ~500
#      lines. (No saving over PA: this proof is independent of
#      induction.)
#
#   4. ``godel_first.py`` (this file, fleshed out) -- diagonal lemma,
#      ``G_Q``, the main theorem, the essential-undecidability
#      corollary, plus the HF model of Q discharging consistency and
#      Sigma_1-soundness. ~400 lines.
#
# Total: ~1450 lines, zero new axioms, no kernel patch. (vs ~1600 for
# the full-PA target.)
#
# Comparison: O'Connor's Coq formalisation (Goedel-Coq) is ~7k LOC;
# Paulson's Isabelle/HOL formalisation is ~12k LOC; Harrison's HOL
# Light formalisation of essential undecidability of Q is ~3k LOC.
# The pyzar estimate is shorter than all of these because (i) HF
# gives Goedel numbering for free, (ii) we inherit ``num`` arithmetic
# from ``nat.py``, and (iii) we are happy with a single specific
# Hilbert-style proof system over Q rather than a generic framework
# parameterised by signature.
#
# Optional extensions:
#   * ``godel_first_pa.py`` -- redo Stages 1-2 with the induction
#     schema and re-export the same incompleteness theorem for PA.
#     ~200 extra lines. Not strictly needed: PA-incompleteness already
#     follows from Q-essential-undecidability via Stage 5's corollary.
#     The standalone PA development is useful only as a stepping stone
#     toward ``godel_second.py``, which *requires* PA's induction.
#   * ``rosser.py`` -- the Rosser predicate variant of Stage 5; ~150
#     lines.
#   * ``tarski.py`` -- Tarski's undefinability of truth as a one-page
#     corollary of the diagonal lemma; ~50 lines.
#
# Recommended ordering:
#   * Do ``hf_sets.py`` first -- this entire file rests on it.
#   * ``q_syntax.py`` is independent of the rest of pyzar's surface
#     theory, so it can be developed in parallel with anything else.
#   * The four object-theory files (``q_syntax``, ``q_proofs``,
#     ``q_repr``, ``godel_first``) form a self-contained subsystem
#     that can be merged as a unit. They are imported again only if
#     someone wants ``godel_second.py`` (which would also pull in the
#     PA extension above).


# ===========================================================================
# Stage 4 -- the diagonal lemma.
# ===========================================================================
#
# Lemma (Goedel-Carnap). For every Q-formula ``phi`` with ``var_x`` as its
# only free variable there exists a Q-sentence ``psi`` such that
#
#     |- Prov_Q (Iff_f psi (substitute phi (numeral psi) var_x)).
#
# Construction (BBJ Ch. 17, Smullyan Ch. 4):
#
#   diag : nat0 -> nat0
#     diag(n) := substitute n (numeral n) var_x.
#
#   D(x, y) : Q-formula representing diag as a binary relation.
#     D(x, y) := substitute_2 substitute_internal x x var_x var_y
#                ``y = substitute(x, x, var_x) = diag(x)`` evaluated in
#                Q via ``substitute_internal``.
#                (specialised: F-slot=t-slot=x, v-slot=var_x,
#                 result-slot=y)
#
#   theta(x) := Exists_f var_y (And_f D(x, y) phi(y))
#                ``x's diagonal-substitute satisfies phi``.
#
#   m   := godelnum(theta) = theta itself (formulas ARE nat0s).
#   psi := substitute theta (numeral m) var_x.
#
# Then godelnum(psi) = diag(m), so when we substitute psi's numeric code
# back, the internal D evaluates to the right value, and Q derives
#     psi  <=>  phi(numeral psi).
#
# AXIOMATIZED for now via ``p.sorry()``: the proof requires substantial
# substitution-pushing in Q (~200-400 lines) and consumes the Stage 3C
# ``SUBSTITUTE_REPRESENTS`` axiom. Posted as ``DIAGONAL_LEMMA`` against
# the Stage-3D side conditions ``IS_FORM_PROV_Q_INTERNAL`` /
# ``FREE_IN_PROV_Q_INTERNAL`` so Stage 5 can apply it directly to
# ``phi := Not_f Prov_Q_internal``.
# ===========================================================================

from fusion import Var
from basics import mk_const, mk_app, mk_abs
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof
from tactics import SPECL, MP
from q_syntax import (
    Not_f,
    Imp_f,
    Forall_f,
    SUBSTITUTE_AT_NOT,
    SUBSTITUTE_AT_IMP,
    SUBSTITUTE_AT_FORALL_MISS,
)
from q_proof import var_x, var_y
from q_repr import (
    numeral,
    substitute,
)


# ---------------------------------------------------------------------------
# Stage 4 (a) -- derived Q-formula connectives on godelnums.
#
# Q's primitive connectives are ``Imp_f`` and ``Not_f`` (plus ``Eq_f``,
# ``Forall_f`` for atom / quantifier). The remaining connectives are
# defined as HOL functions building the corresponding nat0 godelnums:
#
#   And_f a b    := Not_f (Imp_f a (Not_f b))
#   Or_f a b     := Imp_f (Not_f a) b
#   Iff_f a b    := And_f (Imp_f a b) (Imp_f b a)
#   Exists_f v f := Not_f (Forall_f v (Not_f f))
# ---------------------------------------------------------------------------


_a_n0 = Var("a", nat0_ty)
_b_n0 = Var("b", nat0_ty)
_v_n0 = Var("v", nat0_ty)
_f_n0 = Var("f", nat0_ty)


AND_F_DEF = define(
    "And_f",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(
        _a_n0, mk_abs(_b_n0, mk_app(Not_f, mk_app(Imp_f, _a_n0, mk_app(Not_f, _b_n0))))
    ),
)
And_f = mk_const("And_f", [])


OR_F_DEF = define(
    "Or_f",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(_a_n0, mk_abs(_b_n0, mk_app(Imp_f, mk_app(Not_f, _a_n0), _b_n0))),
)
Or_f = mk_const("Or_f", [])


IFF_F_DEF = define(
    "Iff_f",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(
        _a_n0,
        mk_abs(
            _b_n0,
            mk_app(And_f, mk_app(Imp_f, _a_n0, _b_n0), mk_app(Imp_f, _b_n0, _a_n0)),
        ),
    ),
)
Iff_f = mk_const("Iff_f", [])


EXISTS_F_DEF = define(
    "Exists_f",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(
        _v_n0,
        mk_abs(_f_n0, mk_app(Not_f, mk_app(Forall_f, _v_n0, mk_app(Not_f, _f_n0)))),
    ),
)
Exists_f = mk_const("Exists_f", [])


# Pointwise-applied form of each connective definition: useful as a
# rewrite rule (REWRITE_PROVE doesn't beta-reduce, so the bare DEF
# theorems don't fire under an applied And_f / Or_f / Iff_f).
from tactics import AP_THM, BETA_CONV, TRANS as _TRANS_, GENL  # noqa: E402 -- needed only after definitions above
from basics import rand  # noqa: E402 -- paired with the lazy tactics import above


def _at2(def_th, x, y):
    th_x = AP_THM(def_th, x)
    th_x = _TRANS_(th_x, BETA_CONV(rand(th_x._concl)))
    th_xy = AP_THM(th_x, y)
    th_xy = _TRANS_(th_xy, BETA_CONV(rand(th_xy._concl)))
    return GENL([x, y], th_xy)


# |- !a b. And_f a b = Not_f (Imp_f a (Not_f b)).
AND_F_AT = _at2(AND_F_DEF, _a_n0, _b_n0)
# |- !a b. Or_f a b = Imp_f (Not_f a) b.
OR_F_AT = _at2(OR_F_DEF, _a_n0, _b_n0)
# |- !a b. Iff_f a b = And_f (Imp_f a b) (Imp_f b a).
IFF_F_AT = _at2(IFF_F_DEF, _a_n0, _b_n0)
# |- !v f. Exists_f v f = Not_f (Forall_f v (Not_f f)).
EXISTS_F_AT = _at2(EXISTS_F_DEF, _v_n0, _f_n0)


# ---------------------------------------------------------------------------
# Stage 4 (a.1) -- substitution-pushing lemmas for derived connectives.
#
# substitute distributes over And_f / Or_f / Iff_f unconditionally and
# over Exists_f under the side condition ``~(v = bvar)`` (mirroring
# Forall_f). Each is a one-line ``by_rewrite`` chain through the
# connective's defining equation + the primitive substitute equations
# from q_syntax.
# ---------------------------------------------------------------------------


@proof
def SUBSTITUTE_AT_AND(p):
    """|- !a b t v. substitute (And_f a b) t v
    = And_f (substitute a t v) (substitute b t v)."""
    p.goal(
        "!a b t v. substitute (And_f a b) t v = "
        "And_f (substitute a t v) (substitute b t v)"
    )
    p.fix("a b t v")
    p.thus(
        "substitute (And_f a b) t v = And_f (substitute a t v) (substitute b t v)"
    ).by_rewrite([AND_F_AT, SUBSTITUTE_AT_NOT, SUBSTITUTE_AT_IMP])


@proof
def SUBSTITUTE_AT_OR(p):
    """|- !a b t v. substitute (Or_f a b) t v
    = Or_f (substitute a t v) (substitute b t v)."""
    p.goal(
        "!a b t v. substitute (Or_f a b) t v = "
        "Or_f (substitute a t v) (substitute b t v)"
    )
    p.fix("a b t v")
    p.thus(
        "substitute (Or_f a b) t v = Or_f (substitute a t v) (substitute b t v)"
    ).by_rewrite([OR_F_AT, SUBSTITUTE_AT_NOT, SUBSTITUTE_AT_IMP])


@proof
def SUBSTITUTE_AT_IFF(p):
    """|- !a b t v. substitute (Iff_f a b) t v
    = Iff_f (substitute a t v) (substitute b t v)."""
    p.goal(
        "!a b t v. substitute (Iff_f a b) t v = "
        "Iff_f (substitute a t v) (substitute b t v)"
    )
    p.fix("a b t v")
    p.thus(
        "substitute (Iff_f a b) t v = Iff_f (substitute a t v) (substitute b t v)"
    ).by_rewrite(
        [
            IFF_F_AT,
            AND_F_AT,
            SUBSTITUTE_AT_NOT,
            SUBSTITUTE_AT_IMP,
        ]
    )


@proof
def SUBSTITUTE_AT_EXISTS_MISS(p):
    """|- !w body t v. ~(v = w) ==>
            substitute (Exists_f w body) t v
            = Exists_f w (substitute body t v).

    Capture-avoidance side condition: the bound variable index ``w`` of
    the existential must not be the variable being substituted.
    """
    p.goal(
        "!w body t v. ~(v = w) ==> "
        "substitute (Exists_f w body) t v = "
        "Exists_f w (substitute body t v)"
    )
    p.fix("w body t v")
    p.assume("hne: ~(v = w)")
    forall_miss_at = SPECL(
        [p._parse("w"), p._parse("Not_f body"), p._parse("t"), p._parse("v")],
        SUBSTITUTE_AT_FORALL_MISS,
    )
    forall_miss_app = MP(forall_miss_at, p.fact("hne"))
    p.thus(
        "substitute (Exists_f w body) t v = Exists_f w (substitute body t v)"
    ).by_rewrite([EXISTS_F_AT, SUBSTITUTE_AT_NOT, forall_miss_app])


# ---------------------------------------------------------------------------
# Stage 4 (b) -- the diagonal substitution function.
#
#   diag(n) := substitute n (numeral n) var_x
#
# ``diag`` is a HOL function on godelnums. Its representability inside
# Q follows from ``SUBSTITUTE_REPRESENTS`` specialised with F=t=n,
# v=var_x: each instance ``diag(n) = k`` is Q-provable via the
# ``substitute_internal`` formula at numeral arguments.
# ---------------------------------------------------------------------------


_n_diag = Var("n", nat0_ty)


DIAG_DEF = define(
    "diag",
    parse_type("nat0 -> nat0"),
    mk_abs(_n_diag, mk_app(substitute, _n_diag, mk_app(numeral, _n_diag), var_x)),
)
diag = mk_const("diag", [])


# ---------------------------------------------------------------------------
# Stage 4 (b.1) -- diag_internal: representing diag inside Q (AXIOMATIZED).
#
# ``diag_internal`` is a Q-formula in two free variables (``var_x`` for
# the input, ``var_y`` for the output) expressing the relation
# ``var_y = diag(var_x)``. Three axioms (all sorry'd):
#
#   * ``DIAG_REPRESENTS``     : !n. Prov_Q (substitute_2 diag_internal
#                                              (numeral n)
#                                              (numeral (diag n))
#                                              var_x var_y).
#   * ``IS_FORM_DIAG_INTERNAL``  : is_form diag_internal.
#   * ``FREE_IN_DIAG_INTERNAL``  : !v. free_in diag_internal v
#                                       <=> (v = var_x \/ v = var_y).
#
# Justification: ``diag(n) = substitute n (numeral n) var_x`` is the
# composition of two primitive recursive functions (substitute and
# numeral), each representable in Q via Sigma_1 formulas. The combined
# representation factors through ``substitute_internal`` (Stage 3C(a))
# and ``numeral_internal`` (deferred). We axiomatize ``diag_internal``
# directly to bypass the intermediate ``numeral_internal`` step.
#
# Planned alternative discharge path (Q + HF strengthening; see the
# PROPOSED EXTENSION block at the end of q_proof.py's Q-axiom list):
#
#   * ``numeral_internal(x, y) := In y (Insert y Empty) /\ ...`` --
#     numerals are concrete Pair_ord-tagged HF terms; the trace
#     witnessing ``y = numeral x`` is an HF set of (k, numeral k)
#     pairs for k <= x, verified by structural induction on x via
#     foundation Q12.
#   * ``diag_internal := substitute_internal[F:=var_x, t:=numeral_internal,
#                                            v:=var_x, r:=var_y]``
#     -- composition of substitute_internal with numeral_internal,
#     both Sigma_1, expressible in Q + HF without any further
#     sequence-coding machinery.
#   * DIAG_REPRESENTS / DIAG_FUNCTIONAL: forward direction by
#     exhibiting the composite trace HF set; functionality from
#     SUBSTITUTE_REPRESENTS uniqueness + HF extensionality (Q11).
#   * Lines: ~80 vs ~400 in the beta-function path.
# ---------------------------------------------------------------------------


from fusion import new_constant  # noqa: E402 -- registers the constant only at this point


new_constant("diag_internal", nat0_ty)
diag_internal = mk_const("diag_internal", [])


@proof
def DIAG_REPRESENTS(p):
    """|- !n. Prov_Q (substitute_2 diag_internal
                       (numeral n) (numeral (diag n)) var_x var_y).

    Stage 4(b.1) representability of diag. AXIOMATIZED via
    ``p.sorry()``.
    """
    p.goal(
        "!n. Prov_Q (substitute_2 diag_internal "
        "             (numeral n) (numeral (diag n)) var_x var_y)"
    )
    p.sorry()


@proof
def IS_FORM_DIAG_INTERNAL(p):
    """|- is_form diag_internal. AXIOMATIZED."""
    p.goal("is_form diag_internal")
    p.sorry()


@proof
def FREE_IN_DIAG_INTERNAL(p):
    """|- !v. free_in diag_internal v <=> (v = var_x \\/ v = var_y).
    AXIOMATIZED."""
    p.goal("!v. free_in diag_internal v = (v = var_x \\/ v = var_y)")
    p.sorry()


@proof
def DIAG_FUNCTIONAL(p):
    """|- !n. Prov_Q (Forall_f (SUC0 0)
                       (Imp_f (substitute_2 diag_internal
                                 (numeral n) var_y var_x var_y)
                              (Eq_f var_y (numeral (diag n))))).

    Functionality of diag's representation: ``D(numeral n, y) -> y =
    numeral (diag n)``, universally quantified over y. This is the
    second half of representability of a function (uniqueness); the
    first half is ``DIAG_REPRESENTS`` (existence: D holds at the
    correct y). AXIOMATIZED.

    Used in the diagonal lemma's forward direction to identify the
    existential witness ``y_0`` with ``numeral psi``.
    """
    p.goal(
        "!n. Prov_Q (Forall_f (SUC0 0) "
        "             (Imp_f (substitute_2 diag_internal "
        "                      (numeral n) var_y var_x var_y) "
        "                    (Eq_f var_y (numeral (diag n)))))"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 4 (b.2) -- theta-of-phi: the parametric self-referential carrier.
#
# Given ``phi`` with only ``var_x`` free, the diagonal construction
# builds
#
#   theta(phi) := Exists_f (SUC0 0)
#                          (And_f diag_internal
#                                 (substitute phi var_y var_x)).
#
# The bound index ``SUC0 0`` matches the index encoded by ``var_y =
# Var_t (SUC0 0)``: substituting ``var_y`` for ``var_x`` in phi puts
# var_y free in the body, then ``Exists_f (SUC0 0) ...`` binds it.
#
# Reading: "there exists y such that y = diag(x) and phi(y)". When ``x``
# is set to ``numeral m`` for ``m = theta(phi)``, the formula says
# "phi(numeral (diag m))" -- which is "phi(numeral psi)" since
# ``psi = diag m``.
# ---------------------------------------------------------------------------


_phi_n0 = Var("phi", nat0_ty)


from nat0 import ZERO, mk_suc0  # noqa: E402 -- imported here for use in the theta_of_phi definition


# theta_of_phi(phi) := Exists_f (SUC0 0)
#                                (And_f diag_internal
#                                       (substitute phi var_y var_x))
THETA_OF_PHI_DEF = define(
    "theta_of_phi",
    parse_type("nat0 -> nat0"),
    mk_abs(
        _phi_n0,
        mk_app(
            Exists_f,
            mk_suc0(ZERO),
            mk_app(And_f, diag_internal, mk_app(substitute, _phi_n0, var_y, var_x)),
        ),
    ),
)
theta_of_phi = mk_const("theta_of_phi", [])


# ---------------------------------------------------------------------------
# Stage 4 (b.3) -- HOL-level substitute / free_in / is_form lemmas.
#
# Five stubs the diagonal-lemma proof needs at the HOL level (not at
# the Prov_Q level). All derivable from the SUBSTITUTE_AT_* and
# FREE_IN_AT_* recursion equations in q_syntax by structural induction
# on F (or by direct calculation for the concrete inequalities).
# ---------------------------------------------------------------------------


@proof
def VAR_X_NEQ_SUC0_0(p):
    """|- ~(var_x = SUC0 0).

    Concrete inequality. ``var_x = Var_t 0`` is a Pair_ord-encoded
    nat0 (tag-prefixed); ``SUC0 0 = 1`` is a small numeral. Disjoint
    by tag analysis through the Pair_ord encoding.

    Used as the side condition for SUBSTITUTE_AT_EXISTS_MISS when
    pushing substitution through ``theta_of_phi``'s outer
    ``Exists_f (SUC0 0) ...``. STUB.
    """
    p.goal("~(var_x = SUC0 0)")
    p.sorry()


@proof
def VAR_Y_NEQ_VAR_X(p):
    """|- ~(var_y = var_x).

    Concrete inequality between two Q-variable godelnums. From
    VAR_T_INJ + ~(0 = SUC0 0) (= NAT0_NEQ_SUC0_0, derivable via NAT0
    constructor disjointness).

    Used to ensure capture-avoidance when substituting var_y for var_x
    inside phi during the theta_of_phi construction. STUB.
    """
    p.goal("~(var_y = var_x)")
    p.sorry()


@proof
def SUBSTITUTE_PRESERVES_IS_FORM(p):
    """|- !F t v. is_form F /\\ is_term t ==> is_form (substitute F t v).

    Substitution into a well-formed Q-formula (replacing a variable
    index by a well-formed Q-term) yields a well-formed Q-formula.
    Strong induction on F using SUBSTITUTE_AT_* equations and the
    is_form constructor closure lemmas (IS_FORM_AT_EQ / NOT / IMP /
    FORALL). STUB.

    Used to derive ``is_form (diag (theta_of_phi phi))`` for the
    well-formedness conjunct of DIAGONAL_LEMMA's conclusion.
    """
    p.goal(
        "!F t v. is_form F /\\ is_term t ==> is_form (substitute F t v)",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def SUBSTITUTE_FREE_NO_OP(p):
    """|- !F t v. ~(free_in F v) ==> substitute F t v = F.

    Substituting a variable index that doesn't occur free is a no-op.
    Strong induction on F using SUBSTITUTE_AT_* and FREE_IN_AT_*
    equations. STUB.

    Used to compute psi's shape: phi_y := substitute phi var_y var_x
    has var_x not free (since phi has only var_x free, and that var_x
    got replaced by var_y), so substituting again at var_x is no-op.
    """
    p.goal(
        "!F t v. ~(free_in F v) ==> substitute F t v = F",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def FREE_IN_SUBSTITUTE_AT_DIFFERENT_VAR(p):
    """|- !F t v w. ~(v = w) /\\ ~(free_in F v) /\\ ~(free_in t v)
                    ==> ~(free_in (substitute F t w) v).

    Free-variable analysis under substitution: if ``v`` is not free in
    ``F`` and not free in the replacement term ``t``, and ``v`` is
    distinct from the variable index ``w`` being substituted, then
    ``v`` is not free in the substituted result. Strong induction on
    F. STUB.

    Used in the diagonal lemma's forward direction to discharge the
    ``~(free_in (phi[numeral psi / var_x]) (SUC0 0))`` side condition
    of PROV_Q_EXISTS_ELIM.
    """
    p.goal(
        "!F t v w. ~(v = w) /\\ ~(free_in F v) /\\ ~(free_in t v) "
        "==> ~(free_in (substitute F t w) v)",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty, "w": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 4 (c) -- the diagonal lemma (AXIOMATIZED).
#
# Headline:
#   |- !phi. is_form phi
#         /\ (!v. free_in phi v ==> v = var_x)
#         ==> ?psi. is_form psi
#                 /\ Prov_Q (Iff_f psi
#                            (substitute phi (numeral psi) var_x)).
#
# Proof sketch (deferred via p.sorry()):
#   * Build D(var_x, var_y) := substitute_2 substitute_internal var_x
#                              var_x var_x var_y
#     (specialising substitute_internal to F=t=var_x, output=var_y).
#   * theta := Exists_f var_y (And_f D phi_at_y).
#   * Set m := theta; psi := substitute theta (numeral m) var_x.
#   * From SUBSTITUTE_REPRESENTS at F=t=m, derive Q proves D(numeral m,
#     numeral (diag m)).
#   * Hence Q proves theta(numeral m) <=> phi(numeral (diag m)) =
#     phi(numeral psi). Since psi = theta(numeral m), this is the
#     diagonal equivalence.
# ---------------------------------------------------------------------------


@proof
def DIAGONAL_LEMMA(p):
    """|- !phi. is_form phi
              /\\ (!v. free_in phi v ==> v = var_x)
              ==> is_form (diag (theta_of_phi phi))
                /\\ Prov_Q (Iff_f (diag (theta_of_phi phi))
                                  (substitute phi
                                              (numeral
                                                (diag (theta_of_phi phi)))
                                              var_x)).

    Stage 4 diagonal lemma -- existence form with explicit witness.
    The Goedel-Carnap construction is:

        psi := diag (theta_of_phi phi)
             = substitute (theta_of_phi phi)
                          (numeral (theta_of_phi phi))
                          var_x.

    The conjunction asserts both the well-formedness of psi and the
    Q-internal diagonal equivalence.

    AXIOMATIZED via ``p.sorry()`` for the Prov_Q part; the
    well-formedness conjunct ultimately follows from
    ``IS_FORM_DIAG_INTERNAL`` plus closure of ``is_form`` under
    Exists_f / And_f / substitute (lemmas not yet proved).

    The Prov_Q part is the heart of the diagonal lemma; its proof
    requires:
      * substitution-pushing through theta_of_phi to compute psi's
        shape (Stage 4(a.1) lemmas + a substitute-idempotence lemma);
      * DIAG_REPRESENTS at n = theta_of_phi phi to assert
        Q proves diag_internal[var_x:=numeral m, var_y:=numeral psi];
      * Q-internal propositional reasoning (iff-introduction,
        existential introduction/elimination) to derive the headline
        equivalence.

    The original existential form ``?psi. ...`` follows by EXISTS at
    psi := diag (theta_of_phi phi).
    """
    p.goal(
        "!phi. (is_form phi /\\ (!v. free_in phi v ==> v = var_x)) ==> "
        "is_form (diag (theta_of_phi phi)) /\\ "
        "Prov_Q (Iff_f (diag (theta_of_phi phi)) "
        "              (substitute phi "
        "                          (numeral (diag (theta_of_phi phi))) "
        "                          var_x))"
    )
    p.sorry()


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 4 (a) -- derived Q-formula connectives.")
    print("    AND_F_DEF    :", pp_thm(AND_F_DEF))
    print("    OR_F_DEF     :", pp_thm(OR_F_DEF))
    print("    IFF_F_DEF    :", pp_thm(IFF_F_DEF))
    print("    EXISTS_F_DEF :", pp_thm(EXISTS_F_DEF))
    print()
    print("Stage 4 (a.1) -- substitution-pushing for connectives.")
    print("    SUBSTITUTE_AT_AND          :", pp_thm(SUBSTITUTE_AT_AND))
    print("    SUBSTITUTE_AT_OR           :", pp_thm(SUBSTITUTE_AT_OR))
    print("    SUBSTITUTE_AT_IFF          :", pp_thm(SUBSTITUTE_AT_IFF))
    print("    SUBSTITUTE_AT_EXISTS_MISS  :", pp_thm(SUBSTITUTE_AT_EXISTS_MISS))
    print()
    print("Stage 4 (b) -- diagonal substitution function.")
    print("    DIAG_DEF     :", pp_thm(DIAG_DEF))
    print()
    print("Stage 4 (b.1) -- diag_internal axioms (SORRY).")
    print("    DIAG_REPRESENTS         :", pp_thm(DIAG_REPRESENTS))
    print("    IS_FORM_DIAG_INTERNAL   :", pp_thm(IS_FORM_DIAG_INTERNAL))
    print("    FREE_IN_DIAG_INTERNAL   :", pp_thm(FREE_IN_DIAG_INTERNAL))
    print("    DIAG_FUNCTIONAL         :", pp_thm(DIAG_FUNCTIONAL))
    print()
    print("Stage 4 (b.2) -- theta-of-phi construction.")
    print("    THETA_OF_PHI_DEF :", pp_thm(THETA_OF_PHI_DEF))
    print()
    print("Stage 4 (b.3) -- HOL-level subst/free_in/is_form lemmas (STUB).")
    print("    VAR_X_NEQ_SUC0_0                  :", pp_thm(VAR_X_NEQ_SUC0_0))
    print("    VAR_Y_NEQ_VAR_X                   :", pp_thm(VAR_Y_NEQ_VAR_X))
    print(
        "    SUBSTITUTE_PRESERVES_IS_FORM      :", pp_thm(SUBSTITUTE_PRESERVES_IS_FORM)
    )
    print("    SUBSTITUTE_FREE_NO_OP             :", pp_thm(SUBSTITUTE_FREE_NO_OP))
    print(
        "    FREE_IN_SUBSTITUTE_AT_DIFFERENT_VAR :",
        pp_thm(FREE_IN_SUBSTITUTE_AT_DIFFERENT_VAR),
    )
    print()
    print("Stage 4 (c) -- diagonal lemma (SORRY: Prov_Q part).")
    print("    DIAGONAL_LEMMA :", pp_thm(DIAGONAL_LEMMA))
