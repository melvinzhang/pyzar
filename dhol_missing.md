# DHOL kernel: what's still missing

Audit of `fusion_dhol.py` vs. Rothgang/Rabe/Benzmüller's DHOL.

## Shipped since the last audit

- ✓ `etaPi` — `ETA(t_th: typing_thm)` produces `⊢ t = λx:A. t x`.
- ✓ `EQ_TY_CONV` — validity-level conversion: `⊢ s =A t` + `⊢ A ≡ B` → `⊢ s =B t`, with hypothesis propagation from the type-equality bridge.
- ✓ Certificate-driven equation tagging — `safe_mk_eq(ty, lhs, r)` takes the type explicitly; `REFL`/`BETA`/`ETA`/`MK_COMB`/`ABS`/`DEDUCT_ANTISYM_RULE`/`new_basic_definition` all read from supplied certificates instead of consulting `type_of`. Closes the soundness leak where a `CONV`-d typing_thm's type was silently dropped when it entered a theorem.
- ✓ `TRANS` / `EQ_MP` tag checks — `TRANS` requires both equations to be tagged at the same type (use `EQ_TY_CONV` to align); `EQ_MP` requires the equation's tag to be `bool_ty`.
- ✓ Sequential INST — i-th replacement's expected type uses earlier substitutions (`subst_in_type(tm_theta, x.ty)`).
- ✓ `_vsubst` propagates the substitution into Var / Const / Abs-binder type annotations.
- ✓ `INST_TYPE` Clash/alpha-rename recovery.
- ✓ `type_of` deleted — no kernel rule consults intrinsic types any more; the certificate is the only source of truth for typing inside rules.

## Typing-rule gaps

1. **No `congλ'`.** The paper's lambda-congruence allows the *bound variable's type* to differ between the two sides: `Γ ⊢ A ≡ A'   Γ, x:A ⊢ t =B t'  ⟹  Γ ⊢ λx:A. t =Π(x:A).B λx:A'. t'`. Our `ABS(v, th)` forces the same `v` (and hence the same type) on both sides.
2. **No dependent implication typing.** The paper's `⇒type'` rule lets you assume `F` while type-checking `G` in `F ⇒ G`. Example 3 in the paper (`x = y ⇒ id_x = id_y`) literally can't be type-checked without it — and we'd hit the same wall. We don't have `⇒`/`∀`/`∃` as primitives with their own typing rules; if they're defined via β-reducible constants downstream, the dependency is lost.
3. **No non-emptiness condition** on type declarations (paper's modified rule, §3). Empty dependent types are allowed silently.

## Conversion / definitional equality

4. **`MK_COMB`'s bridge applies only to the domain.** If the codomain types `B[l2/x]` and `B[r2/x]` differ propositionally (e.g. because `l2 ≠ r2` and `B` is dependent), there's no place to supply that bridge. The paper's `congAppl'` doesn't have this issue because the resulting equation is at type `B[l2/x]` (or `B[r2/x]`; symmetric by the term equality) — we should probably take both views and certify with a derived type equality.
5. **Beta is syntactic only.** `BETA` only fires on `Comb(Abs(x, body), x)` — the trivial redex. The paper assumes β-conversion is part of definitional equality at every typing step; our `type_eq` doesn't β-reduce, so a Pi codomain like `(\n. vec n) zero` is *not* judged equal to `vec zero` even definitionally. In practice this surfaces every time `subst_in_type` produces an un-reduced application.

## Kind system

6. **Flat kinds.** `new_type("foo", type_arity=N, term_params=(T1, T2, ...))` lists term-param types as a tuple where later types can't depend on earlier params. Real DHOL kinds are themselves dependent: `K ::= tp | (x:A) → K`. So you can declare `vec : nat → tp` and `matrix : nat → nat → tp` but not, say, a kind where the second arg's type mentions the first.
7. **No kind-level checking on type-arg substitution.** `INST_TYPE` substitutes types for tyvars freely; if the tyvar was used at a position expecting a specific kind, we don't notice.

## Missing definitions

8. **No `new_basic_type_definition`.** Paper's type-introduction recipe (and HOL Light's) is omitted; we have no way to introduce a new dependent type family from a non-emptiness proof.
9. **No dest helpers** (`dest_thm`, `dest_typing`, `dest_eq`, `dest_comb`, `dest_abs`). Trivial to add but absent.
10. **No `freesin`-style hypothesis-tracking helpers** updated for `typing_thm`.

## Soundness perimeter (honest-caller model, accepted)

Soundness rests on callers using the documented kernel API only:

- Construct types via `mk_type` / `mk_arrow`. Raw `Tyapp` / `Pi` dataclasses exist but are public-but-discouraged.
- Construct `typing_thm`s only via `VAR` / `CONST` / `APP` / `LAMBDA` / `CONV`.
- Construct `type_eq_thm`s only via `TY_REFL` / `TY_SYM` / `TY_TRANS` / `TY_CONG_BASE` / `TY_CONG_PI`.
- Construct `thm`s only via `REFL` / `ASSUME` / `BETA` / `ETA` / `TRANS` / `MK_COMB` / `ABS` / `EQ_MP` / `DEDUCT_ANTISYM_RULE` / `INST` / `INST_TYPE` / `EQ_TY_CONV` / `new_axiom` / `new_basic_definition`.

Direct construction of certificate dataclasses, or of raw term/type values intended to bypass the smart constructors, is explicitly out of the threat model. This is the same kind of perimeter HOL Light gets from OCaml module abstraction, without any extra Python machinery. Intrinsic `Var.ty` / `Const.ty` / `Abs.bvar.ty` annotations survive only for alpha-equivalence distinguishability and are not load-bearing for inference.

## Beyond the base paper

11. **No theorem-prover-as-oracle.** The paper's whole story is "type-checking generates HOL proof obligations and ships them to an ATP." Our kernel inverts this: it demands the user supply the obligations as `thm` / `type_eq_thm` witnesses. Fine for an interactive kernel; doesn't recover the paper's automation story.
12. **No predicate subtypes** (`A|p`, paper §4, Figure 2). All the `<:I`/`<:Pi`/`|p tp` etc. rules are absent.
13. **No translation to HOL** (paper §3.2, the PER `A*`, definitions PT1–PT21). The paper's main contribution is the sound+complete embedding; we have nothing analogous, so we can't farm DHOL goals out to LEO-III / cvc5.
14. **No refinement / quotient types** (the follow-up work, arXiv:2507.02855).

## Priorities if you keep going

Highest-leverage next steps, roughly increasing effort:

- **Item 5 (β in `type_eq`)** — fold a head-β step into `_ty_eq` for term-args, so substitution products are recognized definitionally. Five lines. Removes a whole class of bridging boilerplate that's currently needed.
- **Item 4 (`MK_COMB` codomain bridge)** — take an optional second `type_eq_thm` parameter and certify the result at the right codomain. Localized fix.
- **Item 1 (`congλ'`)** — a fully general ABS rule. Useful once propositional binder-type changes start appearing in proofs.
- **Item 8 (`new_basic_type_definition`)** — the only way to get new dependent type families backed by real models.
- **Item 13 (translation to HOL)** — the paper's main artifact. PER predicates, axiom translation, ATP wiring. Worth its own milestone — recovers the paper's automation story.

Items 2, 3, 6, 7 are deeper restructurings. Items 9–10 are housekeeping. Items 11, 12, 14 are extensions beyond the base paper.
