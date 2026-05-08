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
