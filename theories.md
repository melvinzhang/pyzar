# Candidate theories for pyzar formalization

Theories with a slick encoding insight, small axiom budget, and classical
payoff -- in the same spirit as `sets_as_trees.py`, `eudoxus_reals.py`,
`hf_sets.py`, and `godel_first.py`. Roughly ordered by aesthetic
alignment with the existing four sketches.

## Sister files to `godel_first.py` (diagonal-argument family)

### `halting.py` -- Undecidability of the halting problem
Encode Turing machines (or while-programs, or lambda-terms) as HF sets;
the universal machine becomes a primitive recursive predicate; halting
is r.e. but not recursive by Cantor diagonal. Reuses ~half the
representability infrastructure from `q_repr.py`. Many provers note
this is essentially the same theorem as Goedel's first; the
formalization makes that explicit.
- Size: ~600 LOC
- Axioms: zero
- Prereqs: `hf_sets.py`

### `tarski_truth.py` -- Undefinability of arithmetic truth
~50 lines if built on `godel_first.py`'s diagonal lemma; the truth
predicate would let you form the liar. Standalone enough to deserve
its own file purely for the framing.
- Size: ~50 LOC (plus framing)
- Axioms: zero
- Prereqs: `godel_first.py`

## Sister files to `hf_sets.py` (encoding-trick family)

### `ordinals_cnf.py` -- Ordinals up to epsilon_0
Each ordinal in Cantor normal form is a finite tree of smaller
ordinals, hence an HF set, hence a num. Addition, multiplication,
exponentiation, well-foundedness. The natural substrate for
Gentzen-style epsilon_0-induction proofs of PA consistency, and a
clean termination order. Pairs especially well with `godel_first.py`
if you ever want `godel_second.py`.
- Size: ~400 LOC
- Axioms: zero
- Prereqs: `hf_sets.py`

### `padic.py` -- p-adic integers
Z_p as the inverse limit of Z/p^n, equivalently as digit sequences
`num -> fin p`. Each finite level is HF; topology comes from the
ultrametric d(x, y) = p^(-v(x-y)). Slick contrast with
`eudoxus_reals.py`: complete metric ring, totally disconnected, no
Archimedean property.
- Size: ~500 LOC
- Axioms: zero (given `int.py`)
- Prereqs: `int.py`, optionally `hf_sets.py`

## Sister files to `eudoxus_reals.py` (cheap-construction family)

### `polynomial.py` -- Polynomial rings
R[X] for any ring R as `num -> R` with cofinite-zero support. Ring
axioms transparent; division algorithm when R is a field. Prerequisite
for Galois theory, algebraic numbers, formal power series.
- Size: ~400 LOC
- Axioms: zero (given a ring R)

### `free_monoid.py` -- Free monoids and free groups
Words over an alphabet, modulo nothing (free monoid) or modulo
cancellation (free group via reduced words). Foundation for any
combinatorial group theory or formal-language work.
- Size: ~300 LOC
- Axioms: zero

## Decidable theories (the algorithm IS the proof)

### `dlo.py` -- Dense linear orders without endpoints
QE in one page, completeness by back-and-forth, decidability is a
corollary. Tiny, and the canonical warm-up before tackling Presburger
or RCF.
- Size: ~200 LOC
- Axioms: zero

### `presburger.py` -- Decidability of (Z, 0, 1, +, <)
Cooper's algorithm: quantifier elimination over a bounded predicate
language. Once formalized, doubles as a tactic for pure-arithmetic
goals -- directly useful in pyzar's downstream proofs.
- Size: ~500 LOC
- Axioms: zero
- Prereqs: `int.py`

### `rcf.py` -- Decidability of real closed fields (Tarski)
Significantly bigger but the flagship classical result; pairs with
`eudoxus_reals.py` for the model.
- Size: ~2000-3000 LOC
- Axioms: zero
- Prereqs: `eudoxus_reals.py`

## Logic warm-ups

### `prop_completeness.py` -- Propositional logic completeness
Hilbert-style propositional calculus + soundness + completeness via
truth tables / canonical valuations. Same proof shape as Goedel-Henkin
in miniature; useful stepping stone if you ever want first-order
completeness.
- Size: ~250 LOC
- Axioms: zero

### `lambda.py` -- Untyped lambda calculus + Church-Rosser
Tait / Martin-Loef parallel reduction. Famously clean in proof
assistants; HF gives variable handling cheaply via de Bruijn indices.
Optional follow-on: Curry-style simply-typed lambda + strong
normalization (~700 more LOC).
- Size: ~500 LOC
- Axioms: zero
- Prereqs: `hf_sets.py`

## Set-theory expansions (require `sets_as_trees.py`)

### `constructible.py` -- Goedel's L
Closure of empty under definable operations indexed by ordinals.
Yields models of V=L, AC, GCH.
- Size: ~1000 LOC
- Axioms: zero
- Prereqs: `sets_as_trees.py`

### `forcing.py` -- Cohen forcing
Independence proofs (~CH in some extension). Flagship application of
set theory; tight historical bookend with `constructible.py` (together
they give Cohen-Goedel independence of CH).
- Size: ~1500 LOC
- Axioms: zero
- Prereqs: `sets_as_trees.py`

## Recommended top three to do first

1. **`ordinals_cnf.py`** -- small, payoff-rich, unlocks proof theory.
2. **`halting.py`** -- tightest aesthetic match to `godel_first.py`;
   reuses infrastructure.
3. **`presburger.py`** -- pays for itself by becoming an arithmetic
   tactic the rest of pyzar can call.

## Common thread

Across all of these, the slick encoding insight ("X is just HF / num /
nat -> R / a finite tree") collapses what looks like a model-theoretic
construction into a HOL-level computation, and the proofs become
arithmetic plus structural induction.
