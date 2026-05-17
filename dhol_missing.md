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

## Typing-rule gaps

2. **No dependent implication typing.** The 2026 paper makes `⇒` primitive (Rule D, Fig. 4): `Γ ⊢ F : bool   Γ, ▷F ⊢ G : bool  ⟹  Γ ⊢ F ⇒ G : bool` — the well-formedness of `G` may depend on the truth of `F` (Example: `x = y ⇒ f x =B[y] f y` for dependent `f : Πx:A. B`, which needs the assumption to even type-check the RHS). DHOL has exactly two primitive connectives: `=` and `⇒`; everything else (`∧`, `∨`, `¬`, `∀`, `∃`, `true`, `false`) is defined. Currently `fusion_dhol` has neither `⇒` nor a notion of boolean assumptions in `typing_thm._asl` propagating into typing of subterms — `typing_thm._asl` exists but no rule consumes assumptions for typing purposes.

## Conversion / definitional equality

4. **Beta is syntactic only.** `BETA` only fires on `Comb(Abs(x, body), x)` — the trivial redex. The paper assumes β-conversion is part of definitional equality at every typing step; our `type_eq` doesn't β-reduce, so a Pi codomain like `(\n. vec n) zero` is *not* judged equal to `vec zero` even definitionally. In practice this surfaces every time `subst_in_type` produces an un-reduced application.

## Kind system

5. **Flat kinds.** `new_type("foo", type_arity=N, term_params=(T1, T2, ...))` lists term-param types as a tuple where later types can't depend on earlier params. Real DHOL kinds are themselves dependent: `K ::= tp | (x:A) → K`. So you can declare `vec : nat → tp` and `matrix : nat → nat → tp` but not, say, a kind where the second arg's type mentions the first.

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
14. **No `Φ`-contexts on declarations / rank-1 polymorphism in declarations.** The paper allows `a(Φ) : Type` and `c(Φ) : A` where `Φ` is itself a context (type variables, term variables, and assumptions). We have partial polymorphism: `Tyvar` plus `CONST(name, tyin)` instantiates the constant's type variables, and `INST_TYPE` substitutes them in theorems. What's missing:
    - Type symbols can't take type-variable parameters. `new_type` accepts only `type_arity` (a count of unnamed `Tyapp.type_args` slots, filled at use-site with any `hol_type`) and `term_params` (a flat tuple of term-arg types). The paper's `PVec(u:Type, n:N) : Type` has both, in one ordered context.
    - Constants can't take dependent parameter contexts. The paper writes `c(Φ) : A`; at use we instantiate `c φ` and the result is `A[φ]`. We collapse this into "the constant's declared type is just `A`, polymorphism is via Tyvar substitution on `A` only" — equivalent expressivity for many cases, but loses the staged-declaration story.
    - Polymorphic axioms (`(Φ) ▷ F` with `Φ` non-empty in the type-variable component) aren't directly representable; we'd need a Tyvar-quantified `thm`.
15. **No dependent implication ⇒ as primitive.** Sibling of item 2. The 2026 Rule D and the proof rules in Fig. 5 (modus ponens, deduction, propositional extensionality `(PE)`, congruence, `(TND)`) are the canonical formulation. Our `DEDUCT_ANTISYM_RULE` corresponds to `(PE)` and is in place. The other ⇒-driven rules (`(I_3)`-style axiom instantiation, `(MP)`-style modus ponens, the implication-introduction discharging `▷F`) need ⇒ to even state.
16. **No tertium non datur (TND)** as a primitive proof rule (`Γ ⊢ F : bool   Γ ⊢ A ≡ A'   ⟹ Γ ⊢ F ∨ ¬F`-flavoured rule; paper Fig. 5, Rule (TND)). Once ⇒, ¬, ∨ are present, this is a classicality axiom — we have nothing equivalent yet.
17. **Empty types disallowed by construction (deliberate divergence).** The paper allows empty types and explicitly notes that `∀x:A. F ⇒ ∃x:A. F` is *not* a theorem; the choice/Hilbert axioms would be needed to recover that. Our atomic `new_type` requires an inhabitation witness, which makes every declared type non-empty and silently re-enables `∀⇒∃`. Worth flagging as a known deviation rather than a bug.
18. **No model-theoretic harness.** Sections 3-5 (strict models, lax models, term model, Theorems 1-6 — soundness, well-definedness, completeness). These are meta-theorems about the calculus, not implementation gaps in the kernel itself, but they give us the *reference* semantics: any future kernel rule should be discharge-able as preserving lax-model interpretation. There's no infrastructure in `fusion_dhol` for stating model preservation, building counter-models, or running consistency arguments.

## Priorities if you keep going

Highest-leverage next steps, roughly increasing effort:

- **Item 4 (β in `type_eq`)** — fold a head-β step into `_ty_eq` for term-args, so substitution products are recognized definitionally. Five lines. Removes a whole class of bridging boilerplate that's currently needed.
- **Item 2 / 15 (primitive ⇒ with Rule D)** — add `F ⇒ G` as a primitive term former plus the Fig. 5 proof rules; thread boolean assumptions through `typing_thm._asl` so the body of `F ⇒ G` can be typed under `▷F`. Unblocks Example 3 of the 2025 paper and the bulk of the dependent-implication uses in 2026.
- **Item 6 (`new_basic_type_definition`)** — the only way to get new dependent type families backed by real models.
- **Item 13 (function preconditions)** — extend `Pi` / `Abs` with an optional `precondition` field defaulting to `true`. Threading this through `LAMBDA` / `APP` / `P_4` is moderate; the payoff is that the 2026 calculus becomes the kernel's native syntax instead of a sublanguage, and refinement/quotient types (item 12) become reachable.
- **Item 11 (translation to HOL)** — the paper's main artifact. PER predicates, axiom translation, ATP wiring. Worth its own milestone — recovers the paper's automation story.

Items 5, 14 are deeper restructurings (dependent kinds; staged `Φ`-contexts on declarations). Items 7–8 are housekeeping. Items 9, 10, 12, 16, 18 are extensions beyond the base kernel. Item 17 is a known deliberate deviation.
