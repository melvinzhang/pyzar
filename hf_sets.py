"""Hereditarily finite sets via Ackermann's bit-encoding.

SKETCH ONLY -- this file lays out the construction; the proofs are
stubbed with strategy comments rather than executed. The goal is to
build the universe ``HF`` of hereditarily finite sets, with membership
``In``, and to prove every ZF axiom *except* INFINITY as a theorem of
HOL + arithmetic on ``num``. The negation of INFINITY is also a
theorem: in ``HF`` every set is finite. Net axiomatic cost: zero.

This is a useful foundation in its own right (ZF - Infinity is
bi-interpretable with PA -- Ackermann 1937) and a pedagogical warm-up
for the full ``sets_as_trees.py`` story: the Ackermann encoding is
that construction's degenerate finite-branching case, where well-
foundedness comes for free from ``<`` on ``num`` and quotienting is
unnecessary because each set already has a canonical numeric
representative.

------------------------------------------------------------------
The idea (Ackermann 1937)
------------------------------------------------------------------

A natural number ``n`` *is* a hereditarily finite set: write ``n`` in
binary, read off the positions of the 1-bits, and recursively decode
each position as another HF set. So

    0       = {}
    1       = {0}              = {{}}
    2       = {1}              = {{{}}}
    3       = {0, 1}           = {{}, {{}}}
    4       = {2}              = {{{{}}}}
    5       = {0, 2}           = {{}, {{{}}}}
    ...

The recipe collapses to a single arithmetical predicate:

    In x y   <=>   bit x of y is 1
             <=>   (y DIV 2^x) MOD 2 = 1.

The encoding is a bijection between ``num`` and HF, and every ZF
operation on HF becomes an arithmetic operation on ``num``:

    Empty            = 0
    Pair x y         = if x = y then 2^x else 2^x + 2^y
    Union y          = sum over members z of y of (the union-image of z)
                       computed bitwise
    Pow y            = sum over subsets s of (bits of y) of 2^(encode s)
    Repl R y         = bitwise relabel of y via the SELECT-defined R
    Sep P y          = bitwise mask y by the predicate P
    Foundation       = well-ordering of <  on num
    Extensionality   = bit-equality on num

Every clause is a primitive recursive definition over ``num`` -- no
subtype, no quotient, no choice beyond SELECT_AX for the
existential-witness glue.

------------------------------------------------------------------
The HOL encoding hurdle (there isn't one)
------------------------------------------------------------------

Unlike ``sets_as_trees.py``, there is *no* type-theoretic obstruction.
HF is literally ``num``, and ``In`` is literally a primitive recursive
predicate on ``num``. The kernel needs no extensions, no
``new_basic_type_definition`` call is required, and no setoid wrapper
is needed because the encoding is canonical: each HF set has exactly
one numeric name.

If we want a *nominal* type ``hf`` distinct from ``num`` (so users
don't accidentally add two HF sets via natural-number ``+``), the
cheapest move is a one-line subtype:

    hf  :=  new_basic_type_definition "hf" "abs_hf" "rep_hf"
            (|- ?n. n = n)        (i.e. trivially non-empty;
                                   the subtype predicate is ``\\n. T``)

This gives ``hf`` ~ ``num`` as types, with ``rep_hf : hf -> num`` and
``abs_hf : num -> hf`` as the (now non-trivial) coercions. All
operations are then defined on ``hf`` by transport.

(For the rest of this file we abuse notation and write ``In``,
``Empty``, ``Pair``, etc. as if they were defined on ``hf``; the
actual definitions go via ``rep_hf`` / ``abs_hf``.)
"""

# ---------------------------------------------------------------------------
# Stage 1 -- bit operations on num.
# ---------------------------------------------------------------------------
#
# pyzar's ``nat.py`` covers ``+``, ``*``, ``<``, but bit operations are
# not yet there. We add the minimum needed:
#
#   defn:  pow2 n      :=  iterated doubling: pow2 0 = 1; pow2 (S n) = 2 * pow2 n
#   defn:  bit i n     :=  (n DIV pow2 i) MOD 2 = 1
#   defn:  set_bit i n :=  if bit i n then n else n + pow2 i
#   defn:  clr_bit i n :=  if bit i n then n - pow2 i else n
#
# Standard lemmas (all by induction on i or n):
#
#   |- bit i 0 = F
#   |- !i j. bit i (pow2 j) = (i = j)
#   |- !i n. bit i (set_bit i n) = T
#   |- !i j n. ~(i = j) ==> bit j (set_bit i n) = bit j n
#   |- !n m. (!i. bit i n = bit i m) ==> n = m       (bit-extensionality)
#
# Bit-extensionality is the crucial lemma: it identifies ``num`` with
# its set of 1-positions, and is the *only* substantive proof in this
# stage. The standard argument: induct on max(n, m), peel off the
# low bit ``bit 0 n`` and divide by 2; the inductive hypothesis closes
# the case. About 30 lines.
#
# The remaining bitwise infrastructure -- OR, AND, sums of pow2 over
# predicates -- builds on these. ~150 lines total for ``bits.py``.

# ---------------------------------------------------------------------------
# Stage 2 -- HF and In.
# ---------------------------------------------------------------------------
#
# defn:  hf       := subtype of num under the trivially-true predicate
#                    (or just type abbreviation; choice is cosmetic)
#        In x y   :<=>  bit (rep_hf x) (rep_hf y) = T
#
# That's it. Every ZF operation below is now an arithmetic recipe.

# ---------------------------------------------------------------------------
# Stage 3 -- ZF axioms (without Infinity) as theorems.
#
# Each constructor takes ``hf`` arguments and returns an ``hf``,
# accompanied by the characterisation theorem stating its membership
# behaviour. The characterisation theorem is exactly the corresponding
# ZF axiom.
# ---------------------------------------------------------------------------

# EMPTY  -- numeric 0.
#   defn:  Empty := abs_hf 0
#   thm:   |- !x. ~In x Empty                          (matches EMPTY_PROP)
#   proof: bit i 0 = F for all i.

# PAIR x y -- two-bit number.
#   defn:  Pair x y := abs_hf (set_bit (rep_hf x) (set_bit (rep_hf y) 0))
#   thm:   |- !a b. ?p. !x. In x p = (x = a \\/ x = b)   (PAIRING)
#   proof: take p := Pair a b; case-split on whether the queried bit
#          equals rep_hf a or rep_hf b; use bit/set_bit lemmas.

# UNION y -- bitwise OR of the bits of the members of y.
#   defn:  Union y := abs_hf (
#              sum over i < bit-length(rep_hf y) of
#                  (if bit i (rep_hf y) then rep_hf (abs_hf i) else 0)
#                  with bitwise OR instead of +
#          )
#   thm:   |- !a. ?u. !x. In x u = ?z. In x z /\\ In z a       (UNION)
#   proof: the bit at position x in Union y is 1 iff some i is a member
#          of y (bit i (rep_hf y) = 1) such that bit x i = 1 (i.e. x is
#          a member of i). Direct from definitions; no induction needed
#          past the bit-length finite-sum lemma.
#   note:  this is the first place where we need a finite sum / finite
#          bitwise OR. Define ``OR_below n f`` recursively over ``n``;
#          ~20 lines.

# POW y -- enumerate subsets of y's bits.
#   defn:  Pow y := abs_hf (
#              sum over s : bit-subset of (rep_hf y) of pow2 (encode s)
#          )
#          where ``encode s`` keeps only the bits of (rep_hf y) selected
#          by s. Concretely: iterate over ``i < 2^bit-length(rep_hf y)``,
#          map each ``i`` to the corresponding sub-mask of (rep_hf y),
#          and OR a fresh bit at position (sub-mask) into the result.
#   thm:   |- !a. ?p. !x. In x p = Subset x a              (POWERSET)
#   proof: every subset of y has a numeric representative ``m`` with
#          (m AND rep_hf y) = m, and there are 2^{bit-length} such m;
#          show Pow enumerates exactly these. Bit-extensionality closes
#          the equivalence.
#   note:  unlike ``sets_as_trees.py``, *no inaccessibility* is needed.
#          ``Pow`` of a finite set is finite, and ``num`` accommodates
#          arbitrary finite numbers. This is why HF is so cheap.

# REPL R y -- functional image, recursively re-encoded.
#   defn:  Repl R y := abs_hf (
#              OR over i with bit i (rep_hf y) = 1 of
#                  pow2 (rep_hf (R (abs_hf i)))
#          )
#   thm:   |- !a. ?b. !y. In y b = ?x. In x a /\\ y = R x      (REPLACEMENT)
#   proof: for HOL-definable ``R``, the image is computed bit by bit;
#          R need not be functional in any extra sense because HOL's
#          ``=`` on ``hf`` is already extensional. Direct from
#          definitions.
#   note:  the ZF schema "for any *formula* R" becomes, in HOL, "for any
#          *term* R : hf -> hf". This is the standard reading of
#          Replacement in higher-order logic and is strictly stronger
#          than the first-order schema -- another small win from the
#          host metatheory.

# SEPARATION P y -- subset by predicate.
#   defn:  Sep P y := abs_hf (
#              OR over i with bit i (rep_hf y) = 1 /\\ P (abs_hf i)
#                of pow2 i
#          )
#   thm:   |- !P a. ?b. !x. In x b = (In x a /\\ P x)         (SEPARATION)
#   proof: bitwise mask; immediate from bit/AND lemmas.

# EXTENSIONALITY -- by bit-extensionality on num.
#   thm:   |- !a b. (!x. In x a = In x b) ==> a = b
#   proof: unfold In on both sides, get (!i. bit i (rep_hf a) =
#          bit i (rep_hf b)), invoke bit-extensionality, finish with
#          rep_hf injectivity.

# FOUNDATION -- by well-ordering of num.
#   thm:   |- !a. (?x. In x a) ==>
#                 ?x. In x a /\\ ~(?y. In y a /\\ In y x)
#   proof: ``In`` strictly decreases the numeric value (bit i n = T ==>
#          i < n; one-line lemma from pow2 monotonicity). So given any
#          non-empty ``a``, the numerically smallest element x of
#          ``In . a`` cannot have a member also in ``a``: any such y
#          would be smaller still, contradicting minimality.
#   note:  this is the slickest payoff of the encoding -- foundation
#          becomes the well-ordering of the natural numbers, which
#          ``nat.py`` already proves.

# ---------------------------------------------------------------------------
# Stage 4 -- what *cannot* be derived, and what *can* be refuted.
# ---------------------------------------------------------------------------
#
# INFINITY says there is a set ``I`` with ``Empty in I`` and closed
# under successor. In HF, every element is a natural number, every
# natural number has finite bit-length, and a successor-closed set
# would need 1-bits at unboundedly many positions -- impossible.
#
# Concretely:
#   thm:   |- ~ ?I. (?z. In z I /\\ ~?w. In w z) /\\
#                   (!x. In x I ==> ?y. In y I /\\
#                                       !w. In w y = (In w x \\/ w = x))
#   proof: any such ``I`` is a num with infinitely many 1-bits, but
#          every num has bit-length at most ``log2 n + 1`` (formally:
#          bit i n = F whenever pow2 i > n; one-line lemma).
#
# So HF refutes Infinity. This is *not* a defect: HF is the
# *intended* model of "ZF without Infinity", and the Ackermann
# bi-interpretation theorem (PA <==> ZF - Infinity) is one of the
# clean foundational results in the area.
#
# What HF *does* prove that we sometimes forget:
#   * Every finite combinatorial fact (Ramsey-finite, finite graphs,
#     finite groups, etc.) is provable directly inside HF.
#   * All of primitive recursive arithmetic; in fact PA itself, via
#     the bi-interpretation.
#   * Decidability of equality, membership, subset, and so on -- all
#     are decidable predicates on ``num``.
#
# What HF does *not* give:
#   * No reals, no sequences indexed by ``nat`` *as completed objects*,
#     no power set of an infinite set (because there isn't one to take
#     the power set of). For analysis or Cantor's theorem you must
#     leave HF for ``sets_as_trees.py`` (or for a dedicated
#     real-number development like ``eudoxus_reals.py``).

# ---------------------------------------------------------------------------
# Stage 5 -- the bi-interpretation, briefly.
# ---------------------------------------------------------------------------
#
# Ackermann's theorem (1937): PA and ZF - Infinity prove the same
# arithmetic sentences. The forward translation is the encoding above
# (every set is a natural number); the reverse is "the natural
# numbers are the von Neumann ordinals up to omega" (which exist in
# HF as 0, 1, 2, 3, ... = Empty, {Empty}, {Empty, {Empty}}, ...).
#
# In pyzar this means: any theorem provable from the seven
# ``tg_set_theory.py`` axioms *that does not use Infinity or the
# inaccessible TARSKI_A* is also provable directly from ``num`` once
# the constructions in this file are in place. That includes most of
# Sätze 1-150 of Landau (everything not involving completed infinite
# sets at the surface).
#
# No new HOL axiom is needed for the bi-interpretation: it is a meta-
# theorem about provability, witnessed by explicit translation
# functions on the proof terms.

# ---------------------------------------------------------------------------
# Implementation roadmap
# ---------------------------------------------------------------------------
#
# The kernel needs no changes. All work is user-level libraries.
#
#   1. ``bits.py`` -- pow2, bit, set_bit, clr_bit, OR_below, AND_below,
#      bit-extensionality, bit-monotonicity (bit i n = T ==> i < n).
#      Reusable beyond this file. (~150 lines.)
#
#   2. ``hf_sets.py`` (this file, fleshed out) -- the trivial subtype
#      ``hf``, ``In``, the seven constructors (Empty, Pair, Union,
#      Pow, Repl, Sep, Foundation as a derived rule), and the eight
#      characterisation theorems (the ZF axioms minus Infinity, plus
#      ~Infinity). Each constructor is ~20 lines of definition + ~30
#      lines of proof. (~350 lines.)
#
#   3. (optional) ``hf_arith.py`` -- the von Neumann numerals inside
#      HF, plus the PA <-> ZF-Inf translations as concrete functions on
#      ``num``. Lets us reuse ``nat.py`` arithmetic theorems as HF
#      theorems by transport. (~200 lines.)
#
# Total: ~500-700 lines of new code, zero new axioms, no kernel patch.
#
# Comparison: ``sets_as_trees.py`` is ~550-650 lines plus a posted
# inaccessibility axiom; this file is ~500 lines and posts nothing.
# The catch is that ``hf_sets.py`` *cannot host analysis* -- ``omega``
# does not exist as an element of HF. For analysis we still need
# ``sets_as_trees.py`` or ``eudoxus_reals.py``.
#
# Skippable shortcut: most of ``bits.py`` can be inlined into
# ``hf_sets.py`` if we don't expect bit operations to be useful
# elsewhere. The honest tradeoff is that bit-extensionality is a
# self-contained reusable lemma and probably wants its own file the
# moment any other module touches binary representations of ``num``.
#
# Recommended ordering relative to other foundation work:
#   * If the priority is "shortest path to Landau Sätze 1-150 with
#     full ZF surface syntax", do ``hf_sets.py`` first -- no axioms,
#     fastest payoff, and everything ports forward when
#     ``sets_as_trees.py`` lands.
#   * If the priority is "real analysis", skip directly to
#     ``eudoxus_reals.py``; HF won't help there.
#   * If the priority is "the full ZF/Tarski-Grothendieck surface",
#     ``sets_as_trees.py`` subsumes this file but is several times
#     larger and posts an axiom.
