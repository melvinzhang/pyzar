# DHOL kernel: what's still missing

Audit of `fusion_dhol.py` vs. Rothgang/Rabe/Benzmüller's DHOL (TOCL 2025, `arXiv:2305.15382`) plus Rabe's 2026 follow-up `rabe_dholmodels_26.pdf` ("Semantics for Dependently-Typed HOL"). The 2026 paper is the reference definition going forward — it subsumes the 2025 RRB calculus and adds rank-1 polymorphism, function preconditions, and a model theory. Both extensions are now tracked by the kernel; remaining gaps are documented inline under the relevant section below.

## Shipped since the last audit

Soundness / hygiene:
- ✓ `type_of` deleted; certificates are the sole source of typing inside rules.
- ✓ Certificate-driven equation tagging — `safe_mk_eq(ty, lhs, r)` takes the tag explicitly; `REFL`/`BETA`/`ETA`/`MK_COMB`/`ABS`/`DEDUCT_ANTISYM_RULE`/`new_basic_definition` read from supplied certificates instead of `type_of`.
- ✓ `TRANS` / `EQ_MP` tag checks (must align via `EQ_TY_CONV`; `EQ_MP` requires bool tag).
- ✓ `INST_TYPE` Clash/alpha-rename recovery; sequential `INST` (i-th replacement's expected type uses earlier substitutions); `_vsubst` propagates into Var/Const/Abs-binder type annotations.
- ✓ Atomic `new_type` with mandatory inhabitation witness — no uninhabited type can ever exist; no runtime inhabitation state.

Rules:
- ✓ `etaPi` (`ETA`).
- ✓ `EQ_TY_CONV` — validity-level conversion `⊢ s =A t` + `⊢ A ≡ B` → `⊢ s =B t`.
- ✓ `congλ'` — `ABS(v, th, ty_eq=...)` accepts an optional binder-type bridge.
- ✓ `congAppl'` codomain bridge — `MK_COMB(..., cod_eq=...)` witnesses `B[l2/x] ≡ B[r2/x]`.
- ✓ Primitive `==>` + Rule D — `IMP_TYPE` (typing layer), `DISCH` / `MP` (validity).

Language extensions:
- ✓ Unified declaration-context model (items 5 + 14a) — `new_type(name, context, witness)`'s `context` is an ordered telescope of `Tyvar | Var` binders; later entries may reference earlier ones (rank-1 polymorphism interleaved with dependent term params). `mk_type` and `TY_CONG_BASE` take a single shape-matching args list and thread substitutions through.
- ✓ Function preconditions on `Pi` / `λ` (item 13, P2+P3) — `Pi`/`Abs` carry optional `precondition: term | None`. `LAMBDA(v, body_th, precondition=F)` captures F; `APP(f_th, a_th, prec=...)` demands a proof of `F[a/x]`. Threaded through alpha-eq, substitution, instantiation, free-vars, printers. `BETA`/`ETA`/`MK_COMB` reject preconditioned inputs (see residual in §Conversion); other rules transparent.
- ✓ Assumption entries in `new_type` Φ-contexts (item 14, type-declaration half) — `Assume(F)` joins `Tyvar` / `Var` as a binder species; `mk_type` / `TY_CONG_BASE` demand a proof of `F[earlier-subst]`.
- ✓ Staged term-side declarations (item 14, term-declaration half) — `Phi = tuple[Tyvar | Var | Assume, ...]` and `PhiSubst = tuple[hol_type | typing_thm | thm, ...]` are first-class kernel concepts shared with the type side. `new_constant(name, ty, phi=...)` declares `c(Φ) : ty`; `CONST(name, σ)` applies σ to Φ in one step; `new_basic_definition(lhs, rhs_th, phi=...)` emits `[asl] |- c(σ_Φ) = rhs`. `Const` carries `term_args` so chosen Var-arg values survive as part of the term AST (locale-internal nullary appearance). `_apply_phi_subst` (single-σ walk) and `_apply_phi_dual` (LHS+RHS walk) are the shared validators used by `mk_type`/`CONST` and `TY_CONG_BASE`/`TM_CONG_BASE` respectively. Legacy `tyin=` / `prec_proofs=` / `preconds=` paths fully retired; one API surface. `new_type`'s declaration param renamed `context=` → `phi=` for parity with the term side.
- ✓ Term-side congruence (`TM_CONG_BASE`) — analogue of `TY_CONG_BASE` for staged term constants: from per-Φ-slot equations derives `Γ ⊢ c(σ_l) =A[σ_l] c(σ_r)`. Optional `cod_eq` bridges A[σ_l] vs A[σ_r] when the body type's two-side substitutions differ. Closes the structural asymmetry between term- and type-side staged constants.
- ✓ Staged theorems (`StagedThm`, `new_axiom(F, phi=...)`, `interpret(staged, σ)`, `THM_CONG_BASE`) — `(Φ) ▷ F` is now first-class on the theorem side, symmetric with `mk_type` / `CONST` on the declaration sides. `new_axiom` validates Φ-shape (asl entries alpha-match Assume formulas; free Vars / Tyvars must be bound). `interpret(staged, σ)` fans `INST_TYPE` / `INST` / `MP`-against-`DISCH` in one step, reusing `_apply_phi_subst`'s shape check. `THM_CONG_BASE(staged, args)` derives `Γ ⊢ F[σ_l] = F[σ_r]` at bool from per-Φ-slot equations, reusing `_apply_phi_dual`.

## Conversion / definitional equality

4. **Beta is syntactic only.** `BETA` only fires on `Comb(Abs(x, body), x)` — the trivial redex. The paper assumes β-conversion is part of definitional equality at every typing step; our `type_eq` doesn't β-reduce, so a Pi codomain like `(\n. vec n) zero` is *not* judged equal to `vec zero` even definitionally. In practice this surfaces every time `subst_in_type` produces an un-reduced application.

13. **Heterogeneous-precondition congruence is unsupported** (item 13 residual). `BETA`, `ETA`, and `MK_COMB` reject inputs whose Pi/Abs carries a precondition rather than discharge it. `BETA(λx:A|F. t) x → t` would need a `thm` proving F; `ETA(t : Π|F. B)` would build `t = λx:A|F. t x` (RHS Abs needs precondition F threaded); `MK_COMB(f=g : Π|F. B, a=b : A)` would need separate discharges of `F[a/x]` and `F[b/x]` plus a precondition-equality bridge. The shape of the rules is clear; each just needs its own design pass. Also missing: **P4 precondition-subtyping** (`Γ ⊢_T G ⇒ F` ⟹ `Π|F. B <: Π|G. B`), which the paper notes is "almost but not quite derivable from η" — needs a dedicated rule or admissible derivation.

## Declarations

5. **Higher-kinded dependency.** The 2025/26 papers' kind grammar is `K ::= tp | (x:A) → K`. Our `new_type` context telescope handles all kinds *ending* in `tp` (including arbitrary Tyvar/Var/Assume interleavings — see the unified-context entry in "shipped"). What's not yet representable is a type symbol whose *result* of a partial application is itself a kind (kinds of kinds). All concrete examples in the paper use telescope-ending-in-`tp` kinds, so this is theoretical headroom rather than an exercised gap; closing it would need `Kind` as its own datatype.

14. ~~**Staged theorems / polymorphic axioms** (item 14 residual).~~ Shipped — see the `StagedThm` entry in "Language extensions". The remaining locale-layer ergonomics (e.g. staged definitions / staged constants returning `StagedThm` instead of plain `thm`) are downstream concerns, not kernel gaps.

## Missing definitions

6. **No `new_basic_type_definition`.** Paper's type-introduction recipe (and HOL Light's) is omitted; we have no way to introduce a new dependent type family from a non-emptiness proof.
7. **No dest helpers** (`dest_thm`, `dest_typing`, `dest_eq`, `dest_comb`, `dest_abs`). Trivial to add but absent.
8. **No `freesin`-style hypothesis-tracking helpers** updated for `typing_thm`.

## Soundness perimeter (honest-caller model, accepted)

Soundness rests on callers using the documented kernel API only:

- Construct types via `mk_type` / `mk_arrow`. Raw `Tyapp` / `Pi` dataclasses exist but are public-but-discouraged. `INST_TYPE` does not re-check well-formedness of its replacement types; callers who used `mk_type` get that for free, callers who used raw dataclasses are on their own.
- Construct term constants via `new_constant(name, ty, phi=...)` and instantiate via `CONST(name, sigma)`; `sigma` is a `PhiSubst` matching the declared Φ. Direct `Const(name, ty, term_args)` is public-but-discouraged — go through `CONST` so `_apply_phi_subst` validates σ.
- Construct `typing_thm`s only via `VAR` / `CONST` / `APP` / `LAMBDA` / `CONV`.
- Construct `type_eq_thm`s only via `TY_REFL` / `TY_SYM` / `TY_TRANS` / `TY_CONG_BASE` / `TY_CONG_PI`.
- Construct `thm`s only via `REFL` / `ASSUME` / `BETA` / `ETA` / `TRANS` / `MK_COMB` / `ABS` / `EQ_MP` / `DEDUCT_ANTISYM_RULE` / `INST` / `INST_TYPE` / `EQ_TY_CONV` / `THM_CONG_BASE` / `interpret` / `new_basic_definition`.
- Construct `StagedThm`s only via `new_axiom(F, phi=...)`.

Direct construction of certificate dataclasses, or of raw term/type values intended to bypass the smart constructors, is explicitly out of the threat model. This is the same kind of perimeter HOL Light gets from OCaml module abstraction, without any extra Python machinery. Intrinsic `Var.ty` / `Const.ty` / `Abs.bvar.ty` annotations survive only for alpha-equivalence distinguishability and are not load-bearing for inference.

## Deliberate deviations from the paper

17. **Empty types disallowed by construction.** The paper allows empty types and explicitly notes that `∀x:A. F ⇒ ∃x:A. F` is *not* a theorem; the choice/Hilbert axioms would be needed to recover that. Our atomic `new_type` requires an inhabitation witness, which makes every declared type non-empty and silently re-enables `∀⇒∃`. Worth flagging as a known deviation rather than a bug.

## Beyond the base paper

9. **No theorem-prover-as-oracle.** The paper's whole story is "type-checking generates HOL proof obligations and ships them to an ATP." Our kernel inverts this: it demands the user supply the obligations as `thm` / `type_eq_thm` witnesses. Fine for an interactive kernel; doesn't recover the paper's automation story.
10. **No predicate subtypes** (`A|p`, paper §4, Figure 2). All the `<:I`/`<:Pi`/`|p tp` etc. rules are absent.
11. **No translation to HOL** (paper §3.2, the PER `A*`, definitions PT1–PT21). The paper's main contribution is the sound+complete embedding; we have nothing analogous, so we can't farm DHOL goals out to LEO-III / cvc5.
12. **No refinement / quotient types** (the follow-up work, arXiv:2507.02855).
16. **No tertium non datur (TND)** as a primitive proof rule (`Γ ⊢ F : bool   Γ ⊢ A ≡ A'   ⟹ Γ ⊢ F ∨ ¬F`-flavoured rule; paper Fig. 5, Rule (TND)). Once ⇒, ¬, ∨ are present, this is a classicality axiom — we have nothing equivalent yet.
18. **No model-theoretic harness.** 2026 paper §§3–5 (strict models, lax models, term model, Theorems 1–6 — soundness, well-definedness, completeness). These are meta-theorems about the calculus, not implementation gaps in the kernel itself, but they give us the *reference* semantics: any future kernel rule should be discharge-able as preserving lax-model interpretation. There's no infrastructure in `fusion_dhol` for stating model preservation, building counter-models, or running consistency arguments.

## Priorities if you keep going

Highest-leverage next steps, roughly increasing effort:

- **Item 4 (β in `type_eq`)** — fold a head-β step into `_ty_eq` for term-args, so substitution products are recognized definitionally. Five lines. Removes a whole class of bridging boilerplate that's currently needed.
- **Item 6 (`new_basic_type_definition`)** — the only way to get new dependent type families backed by real models.
- **Item 13's residual: P4 precondition-subtyping and heterogeneous-precondition congruence** — `BETA` / `ETA` / `MK_COMB` currently reject preconditioned inputs. Lifting that requires per-side precondition discharge; not hard, but each rule needs its own design.
- **Item 11 (translation to HOL)** — the paper's main artifact. PER predicates, axiom translation, ATP wiring. Worth its own milestone — recovers the paper's automation story.

Items 7–8 are housekeeping. Items 9, 10, 12, 16, 18 are extensions / notational gaps beyond the base kernel. Items 2, 5 (telescope), 13 (P2+P3), and 14 (declarations + theorem side) are fully shipped; item 15 is fully shipped and dropped from the gap list. Item 17 is a known deliberate deviation.
