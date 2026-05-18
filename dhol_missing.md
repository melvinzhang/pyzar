# DHOL kernel: what's still missing

Audit of `fusion_dhol.py` vs. Rothgang/Rabe/Benzmüller's DHOL (TOCL 2025, `arXiv:2305.15382`) plus Rabe's 2026 follow-up `rabe_dholmodels_26.pdf` ("Semantics for Dependently-Typed HOL"). The 2026 paper is the reference definition going forward — it subsumes the 2025 RRB calculus and adds rank-1 polymorphism, function preconditions, and a model theory.

This document tracks only what remains. The kernel as it stands ships rank-1 polymorphism via telescopes, predicate subtypes (with preconditions collapsed onto them), staged theorems / declarations, primitive implication, and the full congruence / conversion surface.

## Conversion / definitional equality

4. **Beta is syntactic only.** `BETA` only fires on `Comb(Abs(x, body), x)` — the trivial redex. The paper assumes β-conversion is part of definitional equality at every typing step; our `type_eq` doesn't β-reduce, so a Pi codomain like `(\n. vec n) zero` is *not* judged equal to `vec zero` even definitionally. In practice this surfaces every time `subst_in_type` produces an un-reduced application.

## Declarations

5. **Higher-kinded dependency.** The 2025/26 papers' kind grammar is `K ::= tp | (x:A) → K`. Our `new_type` context telescope handles all kinds *ending* in `tp` (Tyvar/Var/Assume interleavings). What's not yet representable is a type symbol whose *result* of a partial application is itself a kind (kinds of kinds). All concrete examples in the paper use telescope-ending-in-`tp` kinds, so this is theoretical headroom rather than an exercised gap; closing it would need `Kind` as its own datatype.

## Missing definitions

6. **No `new_basic_type_definition`.** Paper's type-introduction recipe (and HOL Light's) is omitted; we have no way to introduce a new dependent type family from a non-emptiness proof.
7. **No dest helpers** (`dest_thm`, `dest_typing`, `dest_eq`, `dest_comb`, `dest_abs`). Trivial to add but absent.
8. **No `freesin`-style hypothesis-tracking helpers** updated for `typing_thm`.

## Soundness perimeter (honest-caller model, accepted)

Soundness rests on callers using the documented kernel API only:

- Construct types via `mk_type` / `mk_arrow` / `mk_subtype` (or the unified `instantiate(name, σ)` for a declared type). Raw `Tyapp` / `Pi` / `Subtype` dataclasses exist but are public-but-discouraged. `INST_TYPE` does not re-check well-formedness of its replacement types; callers who used the constructors get that for free, callers who used raw dataclasses are on their own.
- Construct term constants via `new_constant(name, ty, phi=...)` and instantiate via `CONST(name, sigma)` (or the unified `instantiate(name, σ)`); `sigma` is a `PhiSubst` matching the declared Φ. Direct `Const(name, ty, term_args)` is public-but-discouraged — go through `CONST` so `_apply_phi_subst` validates σ.
- Construct `typing_thm`s only via `VAR` / `CONST` / `APP` / `LAMBDA` / `CONV` / `RESTRICT` / `UNRESTRICT` / `SUBSUME`.
- Construct `type_eq_thm`s only via `TY_REFL` / `TY_SYM` / `TY_TRANS` / `TY_CONG_BASE` / `TY_CONG_PI`.
- Construct `subtype_thm`s only via `ST_REFL` / `ST_TRANS` / `ST_FORGET` / `ST_REFINE` / `ST_PI_DOMAIN`. Consume them at the typing layer via `SUBSUME`.
- Construct `thm`s only via `REFL` / `ASSUME` / `BETA` / `ETA` / `TRANS` / `MK_COMB` / `ABS` / `EQ_MP` / `DEDUCT_ANTISYM_RULE` / `DISCH` / `MP` / `INST` / `INST_TYPE` / `EQ_TY_CONV` / `THM_CONG_BASE` / `interpret` / `new_basic_definition` / `RESTRICT_PROOF`.
- Construct `StagedThm`s only via `new_axiom(F, phi=...)`.

Direct construction of certificate dataclasses, or of raw term/type values intended to bypass the smart constructors, is explicitly out of the threat model. This is the same kind of perimeter HOL Light gets from OCaml module abstraction, without any extra Python machinery. Intrinsic `Var.ty` / `Const.ty` / `Abs.bvar.ty` annotations survive only for alpha-equivalence distinguishability and are not load-bearing for inference.

## Deliberate deviations from the paper

17. **Empty types disallowed by construction.** The paper allows empty types and explicitly notes that `∀x:A. F ⇒ ∃x:A. F` is *not* a theorem; the choice/Hilbert axioms would be needed to recover that. Our atomic `new_type` requires an inhabitation witness, which makes every declared type non-empty and silently re-enables `∀⇒∃`. Worth flagging as a known deviation rather than a bug.

## Beyond the base paper

9. **No theorem-prover-as-oracle.** The paper's whole story is "type-checking generates HOL proof obligations and ships them to an ATP." Our kernel inverts this: it demands the user supply the obligations as `thm` / `type_eq_thm` witnesses. Fine for an interactive kernel; doesn't recover the paper's automation story.
11. **No translation to HOL** (paper §3.2, the PER `A*`, definitions PT1–PT21). The paper's main contribution is the sound+complete embedding; we have nothing analogous, so we can't farm DHOL goals out to LEO-III / cvc5.
12. **No quotient types** (the follow-up work, arXiv:2507.02855). Structural mirror of predicate subtypes: where `Subtype` refines the inhabitants of A while preserving equality, `Quotient` would preserve inhabitants while coarsening equality. Would add a `Quotient(bvar1, bvar2, relation)` hol_type variant alongside `Subtype`, with intro (`CLASS_OF`), equation intro (`CLASS_EQ`), and a universal-property elim (`QUOTIENT_LIFT`); plus three obligation thms at construction (refl/symm/trans). No subtyping relation to or from `A/~` (unlike `A|p <: A`).
16. **No tertium non datur (TND)** as a primitive proof rule (`Γ ⊢ F : bool   Γ ⊢ A ≡ A'   ⟹ Γ ⊢ F ∨ ¬F`-flavoured rule; paper Fig. 5, Rule (TND)). Once ⇒, ¬, ∨ are present, this is a classicality axiom — we have nothing equivalent yet.
18. **No model-theoretic harness.** 2026 paper §§3–5 (strict models, lax models, term model, Theorems 1–6 — soundness, well-definedness, completeness). These are meta-theorems about the calculus, not implementation gaps in the kernel itself, but they give us the *reference* semantics: any future kernel rule should be discharge-able as preserving lax-model interpretation. There's no infrastructure in `fusion_dhol` for stating model preservation, building counter-models, or running consistency arguments.

## Priorities if you keep going

Highest-leverage next steps, roughly increasing effort:

- **Item 4 (β in `type_eq`)** — fold a head-β step into `_ty_eq` for term-args, so substitution products are recognized definitionally. Five lines. Removes a whole class of bridging boilerplate that's currently needed.
- **Item 6 (`new_basic_type_definition`)** — the only way to get new dependent type families backed by real models.
- **Item 12 (quotient types)** — natural companion to the shipped predicate subtypes; ~250–350 lines following the same AST/intro/elim pattern.
- **Item 11 (translation to HOL)** — the paper's main artifact. PER predicates, axiom translation, ATP wiring. Worth its own milestone — recovers the paper's automation story.

Items 7–8 are housekeeping. Items 5, 9, 16, 18 are theoretical-headroom / extension gaps. Item 17 is a known deliberate deviation.
