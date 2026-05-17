## Typing-rule gaps

1. **No `etaPi`.** The paper's `etaPi : Γ ⊢ t : Π(x:A). B / Γ ⊢ t = λx:A. t x` isn't a rule we expose. Eta-conversion has to be done manually via REFL+ABS, which doesn't always work for free.
2. **No `congλ'`.** The paper's lambda-congruence allows the *bound variable's type* to differ between the two sides: `Γ ⊢ A ≡ A'   Γ, x:A ⊢ t =B t'  ⟹  Γ ⊢ λx:A. t =Π(x:A).B λx:A'. t'`. Our `ABS(v, th)` forces the same `v` (and hence the same type) on both sides.
3. **No dependent implication typing.** The paper's `⇒type'` rule lets you assume `F` while type-checking `G` in `F ⇒ G`. Example 3 in the paper (`x = y ⇒ id_x = id_y`) literally can't be type-checked without it — and we'd hit the same wall. We don't have `⇒`/`∀`/`∃` as primitives with their own typing rules; if they're defined via β-reducible constants downstream, the dependency is lost.
4. **No non-emptiness condition** on type declarations (paper's modified rule, §3). Empty dependent types are allowed silently.

## Conversion isn't fully wired in

5. **No type-level CONV for `thm`s.** `CONV` only re-types a `typing_thm`. Given a regular equation `Γ ⊢ s =A t` and a bridge `A ≡ B`, there's no rule producing `Γ ⊢ s =B t`. The paper's congruence-of-validity covers this implicitly via `congBase'` chaining, but in our kernel you'd have to rebuild the equation from scratch.
6. **`safe_mk_eq` picks the equation's type tag from `type_of(lhs)` alone.** If `type_of(lhs) ≢ type_of(rhs)` definitionally (only propositionally), the resulting `=` constant uses lhs's type — sound only if a bridge is implicitly present elsewhere. We never check.
7. **`MK_COMB`'s bridge applies only to the domain.** If the codomain types `B[l2/x]` and `B[r2/x]` differ propositionally (e.g. because `l2 ≠ r2` and `B` is dependent), there's no place to supply that bridge. The paper's `congAppl'` doesn't have this issue because the resulting equation is at type `B[l2/x]` (or `B[r2/x]`; symmetric by the term equality) — we should probably take both views and certify with a derived type equality.

## Kind system

8. **Flat kinds.** `new_type("foo", type_arity=N, term_params=(T1, T2, ...))` lists term-param types as a tuple where later types can't depend on earlier params. Real DHOL kinds are themselves dependent: `K ::= tp | (x:A) → K`. So you can declare `vec : nat → tp` and `matrix : nat → nat → tp` but not, say, a kind where the second arg's type mentions the first.
9. **No kind-level checking on type-arg substitution.** `INST_TYPE` substitutes types for tyvars freely; if the tyvar was used at a position expecting a specific kind, we don't notice (related to the well-formedness trust gap).

## Substitution

10. **`vsubst` precondition** (the `vsubst(theta)` smart constructor at top level) checks `type_eq(type_of(t), x.ty)` definitionally only. It can't see propositional bridges. Pre-CONV is the workaround inside `INST` but raw `vsubst` for ad-hoc substitution lacks it.
11. **Beta is syntactic only.** `BETA` only fires on `Comb(Abs(x, body), x)` — the trivial redex. The paper assumes β-conversion is part of definitional equality at every typing step; our `type_eq` doesn't β-reduce, so a Pi codomain like `(\n. vec n) zero` is *not* judged equal to `vec zero` even definitionally. In practice this surfaces every time `subst_in_type` produces an un-reduced application.

## Missing definitions

12. **No `new_basic_type_definition`.** Paper's type-introduction recipe (and HOL Light's) is omitted; we have no way to introduce a new dependent type family from a non-emptiness proof.
13. **No dest helpers** (`dest_thm`, `dest_typing`, `dest_eq`, `dest_comb`, `dest_abs`). Trivial to add but absent.
14. **No `freesin`-style hypothesis-tracking helpers** updated for `typing_thm`.

## Soundness perimeter

15. **Well-formedness re-checks** on raw `hol_type` inputs (as discussed — you've accepted this).
16. **Theorem-prover-as-oracle pattern not present.** The paper's whole story is "type-checking generates HOL proof obligations and ships them to an ATP." Our kernel inverts this: it demands the user supply the obligations as `thm`/`type_eq_thm` witnesses. That's fine for an interactive kernel but doesn't recover the paper's automation story.

## Beyond the base paper

17. **No predicate subtypes** (`A|p`, paper §4, Figure 2). All the `<:I`/`<:Pi`/`|p tp` etc. rules are absent.
18. **No translation to HOL** (paper §3.2, the PER `A*`, definitions PT1–PT21). The paper's main contribution is the sound+complete embedding; we have nothing analogous, so we can't farm DHOL goals out to LEO-III / cvc5.
19. **No refinement / quotient types** (the follow-up work, arXiv:2507.02855).

## Priorities if you keep going

If the goal is "more real DHOL" for pyzar, the highest-leverage additions in roughly increasing effort:

- **Item 1 (`etaPi`)** — five-line rule, lots of downstream proofs become possible.
- **Item 5 (`CONV` for `thm`)** — `EQ_TY_CONV(th, eq) : Γ ⊢ s =A t / Γ ⊢ A ≡ B / Γ ⊢ s =B t`. Plugs an actual soundness-relevant gap and is small.
- **Item 11 (β in `type_eq`)** — fold a head-β step into `_ty_eq` for term-args, so substitution products are recognized. Five more lines.
- **Item 12 (`new_basic_type_definition`)** — the only way to get new dependent type families with real models.
- **Item 16 (translation to HOL)** — the paper's main artifact. Major project (PER predicates, axiom translation, ATP wiring). Worth its own milestone.

Items 8, 9, 17 are deep restructurings; items 13–14 are housekeeping.
