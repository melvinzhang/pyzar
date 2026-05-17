# DHOL kernel: what's still missing

Audit of `fusion_dhol.py` vs. Rothgang/Rabe/Benzmüller's DHOL (TOCL 2025, `arXiv:2305.15382`) plus Rabe's 2026 follow-up `rabe_dholmodels_26.pdf` ("Semantics for Dependently-Typed HOL"), which extends the base calculus with rank-1 polymorphism and function preconditions.

## Shipped since the last audit

- ✓ `etaPi` — `ETA(t_th: typing_thm)` produces `⊢ t = λx:A. t x`.
- ✓ `EQ_TY_CONV` — validity-level conversion: `⊢ s =A t` + `⊢ A ≡ B` → `⊢ s =B t`, with hypothesis propagation from the type-equality bridge.
- ✓ Certificate-driven equation tagging — `safe_mk_eq(ty, lhs, r)` takes the type explicitly; `REFL`/`BETA`/`ETA`/`MK_COMB`/`ABS`/`DEDUCT_ANTISYM_RULE`/`new_basic_definition` all read from supplied certificates instead of consulting `type_of`. Closes the soundness leak where a `CONV`-d typing_thm's type was silently dropped when it entered a theorem.
- ✓ `TRANS` / `EQ_MP` tag checks — `TRANS` requires both equations to be tagged at the same type (use `EQ_TY_CONV` to align); `EQ_MP` requires the equation's tag to be `bool_ty`.
- ✓ Sequential INST — i-th replacement's expected type uses earlier substitutions (`subst_in_type(tm_theta, x.ty)`).
- ✓ `_vsubst` propagates the substitution into Var / Const / Abs-binder type annotations.
- ✓ `INST_TYPE` Clash/alpha-rename recovery.
- ✓ `type_of` deleted — no kernel rule consults intrinsic types any more; the certificate is the only source of truth for typing inside rules.
- ✓ Atomic `new_type` with mandatory inhabitation witness (paper's modified non-emptiness rule, §3). `new_type(name, ..., witness=(const_name, const_ty))` declares the type and a witness constant in one transaction; `const_ty`'s head (after Pi-stripping) must match `name`. Bool stays primitive. Result: no uninhabited types can exist in the kernel — soundness is guaranteed by construction, and there's no runtime inhabitation state to track or query (no `inhabited_types()`, no `is_inhabited(ty)`, no propagation through `new_constant`).
- ✓ `congλ'` — `ABS(v, th, ty_eq=...)` accepts an optional binder-type bridge `A ≡ A'`. The LHS uses `v:A`, the RHS uses `Var(v.name, A')`; result is tagged at `Π(v:A). B`. Without `ty_eq` the homogeneous case is unchanged. The bridge's hypotheses are absorbed; `v` must not occur free in them.
- ✓ `congAppl'` codomain bridge — `MK_COMB(f_eq, a_eq, eq=..., cod_eq=...)` now takes a second optional `type_eq_thm` witnessing `B[l2/x] ≡ B[r2/x]` when the substituted codomains differ. Result is tagged at `B[l2/x]` (the LHS view) and `cod_eq`'s hypotheses join the result.
- ✓ Primitive `==>` plus Rule D — `==>` lives in `the_term_constants` at `bool → bool → bool`. `IMP_TYPE(F_th, G_th)` is the dependent-implication typing rule: discharges `F` from the consequent's asl when forming `F ⇒ G : bool`, so a consequent type-checked under `▷F` (e.g. via `ASSUME(F)`-derived bridges) lands as an unconditional bool. `DISCH(F_th, th)` and `MP(imp_th, ant_th)` are the validity-layer pair; together with the existing `DEDUCT_ANTISYM_RULE` (= the paper's `(PE)`) this is the Fig. 5 implication-and-PE fragment.
- ✓ Unified declaration-context model (items 5 + 14a) — `new_type(name, context, witness)` replaces `(type_arity, term_params)` with a single ordered telescope of `Tyvar | Var` binders. Tyvar entries declare rank-1 type-variable parameters in scope for later entries; Var entries declare term parameters whose types may reference any earlier binder (type-var or term-var). `mk_type(tyop, args)` and `TY_CONG_BASE(tyop, args)` take a single args list whose shape matches the declared context; both thread a substitution as they walk so cross-binder dependence is honoured. The flat-arity case is `context=()`; pure rank-1 polymorphism uses Tyvar-only contexts; the old dependent-parameter case uses Var-only contexts. `Tyapp` still stores `(type_args, term_args)` separately for downstream code; the declared context recovers the interleaving when needed.
- ✓ Function preconditions on `Pi` / `λ` (item 13). `Pi` and `Abs` carry an optional `precondition: term | None` field (None ≡ true; default). `LAMBDA(v, body_th, precondition=F)` discharges F (and any v-mentioning assumptions) from `body_th._asl` and captures F as the precondition on both the resulting Pi-type and Abs-term. `APP(f_th, a_th, prec=...)` demands a `thm` proving `F[a/x]` whenever f's Pi has a non-None precondition; the proof's asl is absorbed. `_ty_eq` and `_tm_alpha` compare preconditions; `subst_in_type`, `_vsubst`, `_inst_in_term` propagate substitutions into them; `frees` / `vfree_in` / `tyvars` / `type_vars_in_term` cover them too. `BETA`, `ETA`, and `MK_COMB` reject inputs whose Pi/Abs carries a precondition (would require discharge machinery they don't have); CONV, REFL, ASSUME, ABS, TY_CONG_PI, INST, INST_TYPE all work transparently. Item 13's P4 precondition-subtyping (`G ⇒ F` ⟹ `Π|F. B <: Π|G. B`) is not yet a primitive rule.
- ✓ Constants with declaration-time preconditions (item 14b.1). `new_constant(name, ty, preconds=(F_1, ..., F_k))` stores a tuple of bool term schemas alongside the constant's type (Tyvars in each F_i are substituted at use). `CONST(name, tyin, prec_proofs=(p_1, ..., p_k))` requires one `thm` per declared precondition; each proof's conclusion must alpha-match `F_i[tyin]`; proofs' asls accumulate into the result `typing_thm`. Backwards compatible: `preconds=()` is the default and existing call sites are unchanged.
- ✓ Assumption entries (`▷F`) in `new_type` Φ-contexts (item 14, type-declaration half). Added the `Assume(formula)` binder species alongside `Tyvar` / `Var`. `mk_type` and `TY_CONG_BASE` dispatch on it: each demands a `thm` proving `formula[earlier-substitutions]`. mk_type requires the proof's asl to be empty (since `mk_type` returns a bare `hol_type` with no asl tracking); `TY_CONG_BASE` absorbs the proof's asl and additionally rejects cases where the formula's LHS- and RHS-prefix substitutions differ (per-side discharge not yet implemented).

## Conversion / definitional equality

4. **Beta is syntactic only.** `BETA` only fires on `Comb(Abs(x, body), x)` — the trivial redex. The paper assumes β-conversion is part of definitional equality at every typing step; our `type_eq` doesn't β-reduce, so a Pi codomain like `(\n. vec n) zero` is *not* judged equal to `vec zero` even definitionally. In practice this surfaces every time `subst_in_type` produces an un-reduced application.

## Kind system

5. ~~Flat kinds.~~ Shipped as part of the unified-context refactor — see the "shipped since the last audit" list. `new_type` now takes a `context: tuple[Tyvar|Var, ...]` telescope where each entry may reference any earlier entry. What's still missing is dependent *kinds-of-kinds* (`K ::= tp | (x:A) → K` in the paper's full generality, where the result of a partial application of a type symbol is itself a kind). All concrete examples in the paper use telescope-ending-in-`tp` kinds, which the refactor covers; higher-kinded dependency would need `Kind` as its own datatype.

## Missing definitions

6. **No `new_basic_type_definition`.** Paper's type-introduction recipe (and HOL Light's) is omitted; we have no way to introduce a new dependent type family from a non-emptiness proof.
7. **No dest helpers** (`dest_thm`, `dest_typing`, `dest_eq`, `dest_comb`, `dest_abs`). Trivial to add but absent.
8. **No `freesin`-style hypothesis-tracking helpers** updated for `typing_thm`.

## Soundness perimeter (honest-caller model, accepted)

Soundness rests on callers using the documented kernel API only:

- Construct types via `mk_type` / `mk_arrow`. Raw `Tyapp` / `Pi` dataclasses exist but are public-but-discouraged. `INST_TYPE` does not re-check well-formedness of its replacement types; callers who used `mk_type` get that for free, callers who used raw dataclasses are on their own.
- Construct `typing_thm`s only via `VAR` / `CONST` / `APP` / `LAMBDA` / `CONV`.
- Construct `type_eq_thm`s only via `TY_REFL` / `TY_SYM` / `TY_TRANS` / `TY_CONG_BASE` / `TY_CONG_PI`.
- Construct `thm`s only via `REFL` / `ASSUME` / `BETA` / `ETA` / `TRANS` / `MK_COMB` / `ABS` / `EQ_MP` / `DEDUCT_ANTISYM_RULE` / `INST` / `INST_TYPE` / `EQ_TY_CONV` / `new_axiom` / `new_basic_definition`.

Direct construction of certificate dataclasses, or of raw term/type values intended to bypass the smart constructors, is explicitly out of the threat model. This is the same kind of perimeter HOL Light gets from OCaml module abstraction, without any extra Python machinery. Intrinsic `Var.ty` / `Const.ty` / `Abs.bvar.ty` annotations survive only for alpha-equivalence distinguishability and are not load-bearing for inference.

## Beyond the base paper

9. **No theorem-prover-as-oracle.** The paper's whole story is "type-checking generates HOL proof obligations and ships them to an ATP." Our kernel inverts this: it demands the user supply the obligations as `thm` / `type_eq_thm` witnesses. Fine for an interactive kernel; doesn't recover the paper's automation story.
10. **No predicate subtypes** (`A|p`, paper §4, Figure 2). All the `<:I`/`<:Pi`/`|p tp` etc. rules are absent.
11. **No translation to HOL** (paper §3.2, the PER `A*`, definitions PT1–PT21). The paper's main contribution is the sound+complete embedding; we have nothing analogous, so we can't farm DHOL goals out to LEO-III / cvc5.
12. **No refinement / quotient types** (the follow-up work, arXiv:2507.02855).

## Gaps surfaced by the 2026 model-theory paper

The 2026 paper (Rabe, "Semantics for Dependently-Typed HOL") is the reference definition of the language going forward. It subsumes the 2025 RRB calculus and adds two language extensions plus a model theory. The kernel doesn't yet track either extension.

13. ~~No function preconditions.~~ Shipped (P2 + P3) — see "shipped since the last audit". `Pi`/`Abs` carry an optional precondition; `LAMBDA` / `APP` thread proof obligations. **Still missing:** P4 (precondition-subtyping), and heterogeneous-precondition variants of `BETA` / `ETA` / `MK_COMB` (currently those rules reject preconditioned inputs rather than discharge them).
14. **Partial `Φ`-contexts (most shipped; staged term-side and Tyvar-quantified axioms remain).** The paper allows `a(Φ) : Type` and `c(Φ) : A` where `Φ` is itself a context (type variables, term variables, and assumptions).
    - ~~Type symbols can't take type-variable parameters.~~ Shipped — `new_type` now takes a `context: tuple[Tyvar|Var|Assume, ...]` telescope.
    - ~~`Φ`-entries on type declarations don't admit assumption entries.~~ Shipped — `Assume(F)` is now a valid binder species in `new_type` contexts. mk_type / TY_CONG_BASE discharge the obligation at use sites.
    - ~~Constants can't carry preconditions.~~ Shipped — `new_constant(name, ty, preconds=(...))` and `CONST(name, tyin, prec_proofs=(...))` cover the standalone-`▷F` case.
    - Constants still don't bundle their term parameters into a *staged* Φ-context. The paper writes `c(Φ) : A` and instantiates `c φ` in one step; we still write Pi-chained declarations and use APP chains at the call site. Expressivity-equivalent for plain dependent params; purely a staging/notation gap.
    - Polymorphic axioms (`(Φ) ▷ F` with `Φ` non-empty in the type-variable component) aren't *explicitly* representable. Tyvar polymorphism is already implicit (a `thm` with free Tyvars + `INST_TYPE` is functionally equivalent); term-var quantification reduces to `∀` (definable once Hilbert ε arrives); assumption-entry component reduces to `F ⇒ rest` via the primitive `==>` (already shipped). So this is "already shipped via equivalent encodings", not a kernel-rule gap.
15. ~~No dependent implication ⇒ as primitive.~~ Shipped — see the "shipped since the last audit" list. `IMP_TYPE` (Rule D), `DISCH`, and `MP` are now in the kernel; `DEDUCT_ANTISYM_RULE` already played the role of `(PE)`. The `(TND)` rule is still missing (separate item below).
16. **No tertium non datur (TND)** as a primitive proof rule (`Γ ⊢ F : bool   Γ ⊢ A ≡ A'   ⟹ Γ ⊢ F ∨ ¬F`-flavoured rule; paper Fig. 5, Rule (TND)). Once ⇒, ¬, ∨ are present, this is a classicality axiom — we have nothing equivalent yet.
17. **Empty types disallowed by construction (deliberate divergence).** The paper allows empty types and explicitly notes that `∀x:A. F ⇒ ∃x:A. F` is *not* a theorem; the choice/Hilbert axioms would be needed to recover that. Our atomic `new_type` requires an inhabitation witness, which makes every declared type non-empty and silently re-enables `∀⇒∃`. Worth flagging as a known deviation rather than a bug.
18. **No model-theoretic harness.** Sections 3-5 (strict models, lax models, term model, Theorems 1-6 — soundness, well-definedness, completeness). These are meta-theorems about the calculus, not implementation gaps in the kernel itself, but they give us the *reference* semantics: any future kernel rule should be discharge-able as preserving lax-model interpretation. There's no infrastructure in `fusion_dhol` for stating model preservation, building counter-models, or running consistency arguments.

## Priorities if you keep going

Highest-leverage next steps, roughly increasing effort:

- **Item 4 (β in `type_eq`)** — fold a head-β step into `_ty_eq` for term-args, so substitution products are recognized definitionally. Five lines. Removes a whole class of bridging boilerplate that's currently needed.
- **Item 6 (`new_basic_type_definition`)** — the only way to get new dependent type families backed by real models.
- **Item 13's residual: P4 precondition-subtyping and heterogeneous-precondition congruence** — `BETA` / `ETA` / `MK_COMB` currently reject preconditioned inputs. Lifting that requires per-side precondition discharge; not hard, but each rule needs its own design.
- **Item 11 (translation to HOL)** — the paper's main artifact. PER predicates, axiom translation, ATP wiring. Worth its own milestone — recovers the paper's automation story.

Item 14's only remaining piece is the *staged* term-side (constants bundling their term parameters into a Φ-context instead of a Pi-chain) — and that's a notation/staging gap, not an expressivity one. Items 7–8 are housekeeping. Items 9, 10, 12, 16, 18 are extensions beyond the base kernel. Item 17 is a known deliberate deviation. Items 2, 5, 13, and the bulk of 14 are shipped.
