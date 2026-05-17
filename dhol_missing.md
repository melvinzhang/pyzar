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

13. **No function preconditions** (Fig. 1, the paper's headline feature). The 2026 grammar reads `Πx : A|F. B` and `λx : A|F. t` — every binder may carry a boolean precondition `F` (defaulting to `true` when omitted). Effects on the kernel:
    - `Pi` and `Abs` dataclasses gain a third field `precondition: term` (or `None` ≡ `true`).
    - `LAMBDA` (paper's `P_2`): the body is type-checked under `Γ, x:A, ▷F` — i.e., `typing_thm`'s `_asl` must thread boolean assumptions, and `LAMBDA` adds `F` to that context before recursing.
    - `APP` (paper's `P_3`): `f : Πx:A|F. B` applied to `s : A` requires a `thm` discharging `F[s/x]`; result type stays `B[s/x]`. Currently `APP` takes no such proof.
    - **Precondition-subtyping** (paper's `P_4`): if `⊢_T G ⇒ F`, then anything of type `Πx:A|F. B` also has type `Πx:A|G. B`. The paper calls this "almost but not quite derivable from η" and handles it via type-driven type-checking. We'd need a dedicated rule or admissible derivation.
    - All non-precondition Pi types in the paper are the special case `F = true`. So this extension is backwards-compatible — existing rules just thread an extra defaults-to-true field.
14. **Partial `Φ`-contexts (type-side shipped, term-side still missing).** The paper allows `a(Φ) : Type` and `c(Φ) : A` where `Φ` is itself a context (type variables, term variables, and assumptions).
    - ~~Type symbols can't take type-variable parameters.~~ Shipped — `new_type` now takes a `context: tuple[Tyvar|Var, ...]` telescope, so `pvec : (u:Type, n:nat) → tp` is directly representable. See "shipped since the last audit" for the unified-context entry.
    - Constants still can't take dependent parameter contexts. The paper writes `c(Φ) : A`; at use we instantiate `c φ` and the result is `A[φ]`. We collapse this into "the constant's declared type is just `A`, polymorphism is via Tyvar substitution on `A` only" — equivalent expressivity for many cases, but loses the staged-declaration story.
    - Polymorphic axioms (`(Φ) ▷ F` with `Φ` non-empty in the type-variable component) aren't directly representable; we'd need a Tyvar-quantified `thm`.
    - `Φ`-entries on declarations don't yet admit *assumption* entries (the `▷F` mid-context case); only type-var and term-var binders are accepted by `new_type`'s context check.
15. ~~No dependent implication ⇒ as primitive.~~ Shipped — see the "shipped since the last audit" list. `IMP_TYPE` (Rule D), `DISCH`, and `MP` are now in the kernel; `DEDUCT_ANTISYM_RULE` already played the role of `(PE)`. The `(TND)` rule is still missing (separate item below).
16. **No tertium non datur (TND)** as a primitive proof rule (`Γ ⊢ F : bool   Γ ⊢ A ≡ A'   ⟹ Γ ⊢ F ∨ ¬F`-flavoured rule; paper Fig. 5, Rule (TND)). Once ⇒, ¬, ∨ are present, this is a classicality axiom — we have nothing equivalent yet.
17. **Empty types disallowed by construction (deliberate divergence).** The paper allows empty types and explicitly notes that `∀x:A. F ⇒ ∃x:A. F` is *not* a theorem; the choice/Hilbert axioms would be needed to recover that. Our atomic `new_type` requires an inhabitation witness, which makes every declared type non-empty and silently re-enables `∀⇒∃`. Worth flagging as a known deviation rather than a bug.
18. **No model-theoretic harness.** Sections 3-5 (strict models, lax models, term model, Theorems 1-6 — soundness, well-definedness, completeness). These are meta-theorems about the calculus, not implementation gaps in the kernel itself, but they give us the *reference* semantics: any future kernel rule should be discharge-able as preserving lax-model interpretation. There's no infrastructure in `fusion_dhol` for stating model preservation, building counter-models, or running consistency arguments.

## Priorities if you keep going

Highest-leverage next steps, roughly increasing effort:

- **Item 4 (β in `type_eq`)** — fold a head-β step into `_ty_eq` for term-args, so substitution products are recognized definitionally. Five lines. Removes a whole class of bridging boilerplate that's currently needed.
- **Item 6 (`new_basic_type_definition`)** — the only way to get new dependent type families backed by real models.
- **Item 13 (function preconditions)** — extend `Pi` / `Abs` with an optional `precondition` field defaulting to `true`. Threading this through `LAMBDA` / `APP` / `P_4` is moderate; the payoff is that the 2026 calculus becomes the kernel's native syntax instead of a sublanguage, and refinement/quotient types (item 12) become reachable.
- **Item 11 (translation to HOL)** — the paper's main artifact. PER predicates, axiom translation, ATP wiring. Worth its own milestone — recovers the paper's automation story.

Item 14 has only its term-side and assumption-entry pieces left (constants gaining `Φ`-contexts; polymorphic / assumption-bearing axioms). Items 7–8 are housekeeping. Items 9, 10, 12, 16, 18 are extensions beyond the base kernel. Item 17 is a known deliberate deviation. Items 2, 5, and the type-declaration half of 14 are shipped.
