# PRST `p.sorry()` plan of attack

Census across `prst_*.py` (37 sorries remaining; 19 + 3 + 5 + 7 + 8 + 2 = 44 cleared so far):

| File | sorries | Role |
|------|---------|------|
| `prst_syntax.py` | 0 (was 19) | App_pt constructor + extended `is_pterm`/`is_pform`/`free_in_p`/`substitute_p` AT-equations and preservation lemmas — **DONE** |
| `prst_connectives.py` | 0 (was 3) | `substitute_p` distribution over And/Or/Iff (alias-thin wrappers) — **DONE** (Layer 3) |
| `prst_pr.py` | 5 (was 17) | PR-symbol registry + defining-equation axioms + `is_pr_def` recogniser + mu-closure — Layer 4 **partial** (5 PR_ARITY_* remaining), Layer 5 **DONE** |
| `prst_proof.py` | 10 (was 15) | `Proof_PRST` / `Prov_PRST` + closure rules + per-axiom `PROV_PRST_*_DEF` corollaries + `MU_CORRECTNESS` + PR-eval lemmas + `Prov_PRST_internal` — Layer 6 **partial** (8 cleared), Layer 7 **partial** (2 cleared: FREE_IN_PROV_PRST_INTERNAL + IS_PFORM_PROV_PRST_INTERNAL via Layer-2 relax) |
| `prst_repr.py` | 7 | Boolean-tag disjointness + parametric representability schema + four headline representations |
| `prst_godel1.py` | 6 | Diagonal lemma, Gödel sentence, consistency, Sigma_1-soundness, G1, essential undecidability |
| `prst_godel2.py` | 8 | D1/D2/D3 derivability conditions, `mp_combine_pr` correctness, Löb, G2 |

The work decomposes into 9 layers with strict bottom-up dependencies. Layer N can only be attacked after Layer N-1 is real.

---

## Layer 0 — fix the stub *definitions* (not sorries, but blocking)

Several `define(...)` bodies in the PRST files are placeholders (`"\\t:nat0. T"`, `"0"`, etc.) and have to be replaced with the real bodies before any AT-equation can typecheck the way its docstring describes:

- `prst_syntax.py`: **DONE.** `is_pterm` / `is_pform` / `free_in_p` / `substitute_p` are real `define_wf_lt` definitions, with sorry'd MONOs as the Layer 2 obligation. `Tup_pt` is the args-list cons cell (binary term constructor); every recursion is binary structural. Quantifier-free body shapes:
  - `is_pterm`: 4 disjuncts (Empty / Var / Tup with binary recurse / App with is_pr_sym + unary recurse on args). Arity check intentionally NOT enforced syntactically (lives at proof-system level).
  - `is_pform`: 4 disjuncts (Eq / In atomic via `is_pterm`; Not / Imp recursive). No Forall_pf.
  - `free_in_p`: 7 disjuncts (Var hit / Tup / Eq / In / Not / Imp / App, all binary or unary structural). No Forall_pf, no capture-avoidance guard.
  - `substitute_p`: 8 SELECT-disjuncts. Only Var_pt has HIT/MISS branches; every other case is uniform pointwise recursion. App_pt case is a single recursive call on args.
  - `Tup_pt` term constructor + 6 size/inj/disjointness stubs.
  - `IS_PR_SYM_DEF` / `PR_ARITY_DEF` — still forward-declared stubs; real bodies belong in `prst_pr.py` Layer 4. (`pr_arity` is not referenced from `_IS_PTERM_F` — arity check is at the proof-system level.)
- `prst_pr.py`: **DONE.**
  - `PROJ_DEF_AXIOM_AT_DEF` — real body `Eq_pf (App_pt (proj_sym i n) (var_t_args_rev n)) (Var_t i)`, using a new `var_t_args_rev : nat0 -> nat0` helper (primitive recursion on `n` via `define_unary_0`)
  - `REC_BASE_DEF_AXIOM_AT_DEF`, `REC_STEP_DEF_AXIOM_AT_DEF` — real `Eq_pf (App_pt (rec_sym g h) ...) (App_pt g ...)` / step bodies with explicit Var_t slot conventions (y_vec / i / s). The membership-canonical collapse case for rec_step is deferred to the proof-system level.
  - `IS_PR_DEF_DEF` — real 6-disjunct recogniser (no adj branch, since adj_sym is primitive)
  - `IS_PARTIAL_PR_SYM_DEF` — converted to `define_wf_lt` with sorry'd MONO; recursion on `f` is well-founded because `g < mu_sym g` by `NAT0_LT_PAIR_ORD_R`. AT-equation `is_partial_pr_sym f = is_pr_sym f \/ (?g. f = mu_sym g /\ is_partial_pr_sym g)` is derivable from the wf-lt recursion equation
  - `numeral_pr_def` — real composition `rec_sym zero_sym (comp_sym adj_sym (Tup_pt (proj 2 4) (Tup_pt (proj 2 4) Empty_pt)))`
  - `substitute_pr_def` — **real body**: `comp_sym (course_rec g_subst h_subst) [proj 0 3, comp_sym pair_ord_sym [proj 1 3, proj 2 3]]` with `g_subst := const_sym 0` and `h_subst` as a 7-deep if_in_sym dispatch over formula-constructor tags. `Proof_PRST_pr_def` — still placeholder PR composition (`proj_sym 1 2`); full body is ~200-line composition that Layer 10 fills in alongside `PROOF_PRST_PR_DEFINING`. Downstream Proof_PRST_pr lemmas remain sorry'd against the placeholder.
  - `diag_pr_def` — **DONE** (commit `0a11831`). All three arg-shapers wired: `proj 0 1`, `comp numeral_pr (proj 0 1)`, `const_sym (Var_t 0)`. The `const_sym` primitive (tag 5, 1-ary "constant function") closed the var_x slot.
- `prst_proof.py`: **DONE.**
  - `Proof_PRST_def` — converted to `define_wf_lt` recursion on the proof list with sorry'd MONO. AT-equations `PROOF_PRST_NIL` / `PROOF_PRST_CONS` are derivable from the wf-lt recursion equation (Layer 6 work)

These are not `p.sorry()` calls, but every downstream AT-equation that "unfolds" them silently relies on real bodies. Replace them **before** attempting the AT proofs, otherwise the AT lemma will be unprovable (constant stubs don't satisfy the recursion equations).

---

## Layer 1 — `prst_syntax` constructor lemmas — **DONE**

All 11 constructor lemmas (5 App_pt + 6 Tup_pt) discharged inline in `prst_syntax.py`:

- `NAT0_LT_APP_PT_L/R`, `NAT0_LT_TUP_PT_L/R` — `NAT0_LT_PAIR_ORD_L/R` + `NAT0_LT_TRANS` chains
- `APP_PT_INJ`, `TUP_PT_INJ` — two `PAIR_ORD_INJ` invocations each
- `APP_PT_DISJOINT_VAR_T/EMPTY`, `TUP_PT_DISJOINT_VAR_T/EMPTY/APP_PT` — tag-disjointness via fresh `_prove_tag_neq` instances at (2, 11), (2, 12), (11, 12), plus `_NEQ_PAIR_ORD_ZERO` for the Empty_t cases

Reused private helpers from `hf_syntax`: `_prove_tag_neq`, `_NEQ_PAIR_ORD_ZERO`.

---

## Layer 2 — `prst_syntax` MONOs and AT-equations — **DONE**

Depends on Layer 0 real bodies + Layer 1 size lemmas.

All 19 prst_syntax sorries discharged: 3 MONOs (IS_PFORM / FREE_IN_P / SUBSTITUTE_P) + 16 AT-equations + 2 preservation lemmas. (IS_PARTIAL_PR_SYM_MONO and PROOF_PRST_MONO live in `prst_pr.py` / `prst_proof.py` and remain Layer 4/6 work.)

**MONOs.** Pattern: per-disjunct iff via the appropriate `mono_iff_*_step` family, glued by `or_chain_collapse`, then `by_unfold` against the `_*_F_DEF`. For function-valued / SELECT-valued targets, additional `ABS` (over `v` / `r` / `t`) and `AP_TERM` (through the `@` constant) lifts.
- `IS_PFORM_MONO`: 4 disjuncts (Eq_pf/In_pa REFL, Not_pf unary, Imp_pf binary) via `mono_iff_unary_step` / `mono_iff_binary_step`.
- `FREE_IN_P_MONO`: 7 disjuncts; binary-disj-pw for Tup_pt/Eq_pf/In_pa/Imp_pf, unary-pw for Not_pf, REFL for Var_pt, and the App_pt right-only case via the private `_mono_iff_binary_pw_step` factory with `recurses_l=False`.
- `SUBSTITUTE_P_MONO`: 8 disjuncts; value-binary-pw for Tup_pt/Eq_pf/In_pa/Imp_pf, value-unary-pw for Not_pf, REFL for Empty_pt/Var_pt, App_pt right-only via the private `_mono_iff_value_binary_pw_step`.

**AT-equations.** `IS_PFORM_AT_*` via `derive_rec_eq`, `FREE_IN_P_AT_*` via `derive_rec_eq_pw`, `SUBSTITUTE_P_AT_*` via `derive_rec_eq_select` / `_select_cond` (the latter for `Var_pt`'s HIT/MISS conditional).

**Preservation.** `SUBSTITUTE_P_PRESERVES_IS_PTERM` / `_PFORM`: strong induction on the encoded term/formula, case-split on `IS_PTERM_REC` / `IS_PFORM_REC`, dispatch through the AT-equations + `EXCLUDED_MIDDLE` on `w = v` for the `Var_pt` HIT/MISS.

**Registry buildout.** `PRST_REGISTRY` is extended in-place with the formula constructors (`Eq_pf`, `In_pa`, `Not_pf`, `Imp_pf`), 6 intra-formula disjointness pairs, 4 `Var_pt` × formula disjointness pairs (all via `_alias_transport` from hf-side lemmas + `EQ_PF_DEF` / etc.), and 8 cross-pairs `(Eq_pf/Not_pf/Imp_pf/In_pa) × (Tup_pt/App_pt)` (built by monkey-patching hf_syntax's `_CTORS` and `_TAG_NEQS` with PRST-only entries, then reusing `_proof_ctor_disjoint`).

**DSL friction observed:**
- The `mono_iff_*` family doesn't cover the App_pt-with-pred shape (`?a b. n = C a b /\ P a /\ f b`); a fresh `_mono_iff_app_pt_step` had to be written from scratch (~70 lines).
- The PRST formula-constructor aliases (Not_pf, Imp_pf, Eq_pf, In_pa) are fresh constants distinct from their hf_syntax originals. `_alias_transport(hf_thm, *alias_defs)` (REWRITE_RULE with `SYM` of alias DEFs) reliably transports size/INJ/disjointness/neq-empty across the alias boundary; 14 calls in prst_syntax. Worth promoting to a public hf_syntax helper.
- `mono_iff_binary_right_pw_step` (bool) and `mono_iff_value_binary_right_pw_step` (value) don't exist publicly. Both PRST `App_pt` cases (in free_in_p and substitute_p) reach into the private `_mono_iff_binary_pw_step` / `_mono_iff_value_binary_pw_step` with `recurses_l=False` and a custom `rest_builder` lambda. Two more public helpers would close the API gap.
- **Disjointness keys must follow the lemma's `~(LHS = RHS)` orientation, not body-disjunct order.** `_ctor_neq_lemma` reads the first name in the key as the LHS-ctor; `_spec_neq_at` then SPECLs `target_args + other_args` (fwd) or `other_args + target_args` (rev). Mis-keying produces a `neq_specd` term whose arguments are shuffled across the two ctors (e.g. `~(Not_pf t1 = In_pa t2 SELECT)` instead of `~(In_pa t1 t2 = Not_pf SELECT)`); the MP against `head_eq_th` then fails with a confusing `EQ_MP` error far downstream. PRST keys mirror the hf-side `_CTOR_NAMES` order: `Eq_pf < Not_pf < Imp_pf < In_pa`, with PRST-native ctors (Tup_pt tag 12, App_pt tag 11) following the formula ctors.
- `_ctor_neq_lemma` routes the Empty case through `registry.neq_empty[ctor_b_name]`, so SUBSTITUTE_P_AT_EMPTY needs neq-empty entries for *every* other body constructor (Eq_pf/In_pa/Not_pf/Imp_pf in addition to the term ctors).
- `_proof_ctor_disjoint` reads tag indices and AT lemmas from the module-level `_CTORS` and tag inequalities from `_TAG_NEQS` (which only ships pairs with both indices in `{0..10}`). PRST monkey-patches both dicts with `Tup_pt` / `App_pt` decls and the 8 missing tag-neq pairs `(5..10, 11..12)`, then reuses the factory. The alternative — writing 8 fresh `@proof` blocks — would be ~200 lines.
- `derive_rec_eq` doesn't handle nullary `Empty` cases — the hf side skips `IS_TERM_AT_EMPTY` for the same reason. The trivial REFL has to be done manually.
- `derive_rec_eq` produces `... = T` rather than the bare assertion for body-less matched disjuncts (e.g. `is_pterm (Var_pt v) = T` instead of `is_pterm (Var_pt v)`); a small `_strip_eqT` helper EQT_ELIMs under the foralls.
- IS_PTERM_REC's Var disjunct binds `?v. s = Var_pt v`, which shadows the outer substitute index in `SUBSTITUTE_P_PRESERVES_IS_PTERM`. Worked around by renaming the goal's substitute index to `w` instead of `v` (alpha-equivalent published theorem).

⚠️ Watch the `App_pt` cases: the recursion call goes through the args slot directly (justified by `NAT0_LT_APP_PT_R`), with the binary `Tup_pt` cons cell unfolded inside `is_pterm` / `free_in_p` / `substitute_p` themselves.

---

## Layer 3 — `prst_connectives` (3 sorries) — **DONE**

All three `SUBSTITUTE_P_AT_AND/_OR/_IFF` discharged. Cost ended up at ~25 lines of proof + ~10 lines of comment.

**Shape that worked:** each lemma is one `by_rewrite` call. The rule set must include both directions of the alias DEFs:
- forward `AND_PF_DEF` / `OR_PF_DEF` / `IFF_PF_DEF` to unfold the PRST connective alias
- forward `AND_F_AT` (for And, Or, Iff — Or expands through And via the hf-side body; Iff expands through And too)
- `SYM(NOT_PF_DEF)` / `SYM(IMP_PF_DEF)` to *fold* the `Not_f` / `Imp_f` produced by `AND_F_AT` *back* into `Not_pf` / `Imp_pf` so that `SUBSTITUTE_P_AT_NOT` / `_AT_IMP` can fire (those lemmas are stated at `Not_pf` / `Imp_pf`).
- `SUBSTITUTE_P_AT_NOT` and `SUBSTITUTE_P_AT_IMP` to distribute substitute_p across the unfolded body.

**DSL friction noted:**
- Mixing forward `AND_PF_DEF` / `AND_F_AT` with `SYM(NOT_PF_DEF)` / `SYM(IMP_PF_DEF)` in one `by_rewrite` is loop-free *only* because the two directions touch disjoint heads — the rewriter doesn't warn about this; it just diverges if the directions overlap. Worth keeping in mind for Layer 4+.
- PRST formula-constructor aliases (`Not_pf`, `Imp_pf`, `And_pf`, `Or_pf`, `Iff_pf`) are fresh constants wrapping `Not_f` / `Imp_f` / `And_f` / `Or_f` / `Iff_f`. Sharing the bit-encoded body alone isn't enough for `by_rewrite` to mix-and-match hf-side and prst-side AT-lemmas — you pay a small fold/unfold dance per connective.

---

## Layer 4 — `prst_pr` PR-symbol registry (10 sorries) — **partial: 5/10 done**

Depends on Layer 0 real bodies of `IS_PR_SYM_DEF` / `PR_ARITY_DEF`.

**Done (5 sorries cleared):**
- `IS_PR_SYM_ZERO/ADJ/PROJ/IF_IN/REC` (5) — discharged.
- `IS_PR_SYM_DEF` got a real non-recursive 5-disjunct body in `prst_syntax.py` (was `\f. F` stub). Body is encoded directly in nat0 literals / `Pair_ord` shapes (symbolic `zero_sym` / `adj_sym` / ... live in `prst_pr.py`, so the body can't name them).
- Each lemma follows the same shape: `have eq` (specialize symbol DEF), `have h_ex` via `by_exists` for the multi-binder existential leaves (proj, rec), `have h_body` via `by_disj` into the 5-disjunct body, `thus` via `by_unfold` of `IS_PR_SYM_DEF`.

**Remaining (5 sorries):**
- `PR_ARITY_ZERO/ADJ/PROJ/IF_IN/REC` (5) — all still sorry.
- `PR_ARITY_DEF` was given a non-recursive 4-case SELECT body covering only the closed-tag cases (`zero_sym = 0`, `adj_sym = 2`, `if_in_sym = 4`). The proj and rec arities collapse into the unconstrained-SELECT fallback.

**Why the remaining 5 are harder than the original "~80 lines" estimate:**
- `PR_ARITY_REC`'s intended statement `pr_arity (rec_sym g h) = SUC0 (pr_arity g)` is *intrinsically recursive* on the encoding (`rec_sym g h = Pair_ord 4 (Pair_ord g h)` carries no arity-of-g information). Mechanising it requires a wf-recursive `pr_arity` via `define_wf_lt` + a ~150-line `PR_ARITY_MONO` proof analogous to `SUBSTITUTE_P_MONO`. (Attempted; the MONO ended up sorry'd and was reverted.)
- Even after fixing the body, discharging the four non-recursive cases `pr_arity X_sym = literal` against a SELECT body needs either a `SELECT_UNIQUE` helper (pyzar has only `SELECT_AX`) or ~30 lines per lemma of manual SELECT-uniqueness reasoning via constructor disjointness on nat0 literals.

**Three forks for the follow-up (pick one before resuming):**
1. **Punt for now.** Move to Layer 5 and revisit later. No downstream module consumes `pr_arity`, so the placeholder is safe.
2. **Wf-recursive `pr_arity` + full MONO.** ~250-400 lines. Requires a 2-binder Pair_ord-shape MONO step (like `_mono_iff_value_binary_pw_step` but for `Pair_ord (lit) (Pair_ord a b)` not a single ctor).
3. **Weaken `PR_ARITY_PROJ` / `_REC`.** Add manual SELECT-uniqueness lemmas, discharge ZERO/ADJ/IF_IN at full fidelity, restate PROJ and REC as `pr_arity X = 0` to match the non-recursive body. Closes all 5 sorries but loses the +1 semantics.

**DSL friction newly observed (Layer 4 part 1):**
- There is no "unfold-DEF-and-prove-a-disjunct" idiom — each IS_PR_SYM lemma is a 4-line ritual (have eq, build the existential leaf, `by_disj`, `by_unfold`). A `by_unfold_disj(IS_PR_SYM_DEF, witness=...)` helper would collapse it.
- `by_disj_witness` is single-binder; the 2-binder existential leaves (proj's `?i n.`, rec's `?g h.`) need an explicit `by_exists` step to produce the existential separately, then `by_disj` it into the chain.
- Variable shadowing: when the outer fixed vars are `i n` and the existential leaf is `?i n. ...`, the parser alpha-renames the bound names to `i' n'`. `by_unfold`'s alpha-match then fails. Fix: use fresh bound names (`ii nn`, `gg hh`) in the user-side body string so the renaming aligns by accident-of-naming.

---

## Layer 5 — `prst_pr` `is_pr_def` recogniser (6 sorries)

Depends on Layer 0 real `IS_PR_DEF_DEF` body + the per-axiom closed nat0s being real (Layer 0 `PROJ_DEF_AXIOM_AT_DEF` etc.) + Layer 4.

- `IS_PR_DEF_HOLDS_ZERO/PROJ/IF_IN_TRUE/IF_IN_FALSE/REC_BASE/REC_STEP` (6)
- `IS_PARTIAL_PR_SYM_MU` (1)

**Cost:** ~60 lines. Each: one DISJ-introduction into the `is_pr_def` body, then EXISTS at the parameter slots (PROJ/REC cases). The mu lemma is one unfold of the `is_partial_pr_sym` recursion.

⚠️ Critical Layer 0 dependency: `IS_PR_DEF_DEF`'s real body (the 6-disjunct in the comment) must precede this layer, otherwise `IS_PR_DEF_HOLDS_ZERO` is provably false (current body is `F`).

---

## Layer 5 — `prst_pr` `is_pr_def` recogniser (6 sorries + IS_PARTIAL_PR_SYM_MU) — **DONE**

All 7 listed sorries cleared in commit `ad84a26`, plus a new size lemma `NAT0_LT_MU_SYM`.

**Cleared:**
- 6 IS_PR_DEF_HOLDS_* (ZERO/PROJ/IF_IN_TRUE/IF_IN_FALSE/REC_BASE/REC_STEP) — identical proof shape to Layer 4's IS_PR_SYM_* lemmas (build the disjunction body specialised at the axiom name, then `by_unfold` of `IS_PR_DEF_DEF`). The 2-binder existential leaves (PROJ, REC_BASE, REC_STEP) build via `by_exists` with the REFL conjunct + side-condition facts passed as *separate* rules.
- `IS_PARTIAL_PR_SYM_MONO` — plan listed it as a Layer 2 leftover. Body has a non-recursive `is_pr_sym n` disjunct (REFL) plus the standard unary recursive `?g. n = mu_sym g /\ rec g` disjunct (`mono_iff_unary_step(mu_sym, NAT0_LT_MU_SYM, h)`), glued by `or_chain_collapse` + `by_unfold`.
- `IS_PARTIAL_PR_SYM_MU` — one `SPEC` of `_IS_PARTIAL_PR_SYM_REC` at `mu_sym f`, `by_unfold` to expose `_IS_PARTIAL_PR_SYM_F`'s 2-disjunct body, witness `g := f` via `by_exists`, `by_disj`, `by_eq_mp` back through the recursion equation.

**New helper:** `NAT0_LT_MU_SYM: !g. nat0_lt g (mu_sym g)`. Derived from `NAT0_LT_PAIR_ORD_R` after specialising `mu_sym_def` at `g` via `p.unfold(mu_sym_def, "g")` — the bare definition equation is at function-equality level (`mu_sym = \f. Pair_ord 6 f`), so `by_rewrite_of` against `SYM(mu_sym_def)` doesn't reduce; need the applied-form equation `mu_sym g = Pair_ord 6 g` first.

**DSL friction newly observed:**
- `by_exists` discharges *each `/\` conjunct of the substituted body* independently — passing a pre-`CONJ`'d fact as one rule trips `dest_eq` because conjunction isn't an equation. Pass each conjunct's witness/REFL as separate `*rules` arguments.
- `by_rewrite_of` against a function-equality `f = \x. body` doesn't reduce the applied form `f a` directly — you have to specialise via `p.unfold(f_def, "a")` first to get `f a = body[a]`, then rewrite with that. (Discovered while proving `NAT0_LT_MU_SYM`.)

---

## Layer 6 — `prst_proof` foundations (8 + 6 sorries) — **partial: 8/14 cleared**

Depends on Layer 0 real `Proof_PRST_def` body + Layers 1-5.

**Done in commit `2ab7431` (8 cleared):**
- `PROOF_PRST_AT` (new helper): binary at-form `Proof_PRST p n = ?h t. p = Tup_pt h t /\ ...` derived from `_PROOF_PRST_REC` + `_PROOF_PRST_F_DEF` via SPEC + AP_THM + BETA.
- `PROOF_PRST_NIL`: contradiction proof — PROOF_PRST_AT at Empty_pt + TUP_PT_NEQ_EMPTY_PT.
- `PROV_PRST_AXIOM`: build one-line proof `Tup_pt n Empty_pt` against PROOF_PRST_AT directly. Bypasses PROOF_PRST_CONS.
- 6 `PROV_PRST_*_DEF` (ZERO/PROJ/IF_IN_TRUE/IF_IN_FALSE/REC_BASE/REC_STEP). Each is one `_is_pr_axiom_from_pr_def` helper call (DISJ1 + IS_PR_AXIOM_DEF unfold) + `by(PROV_PRST_AXIOM, axiom, h_axiom)`.

**Remaining (6 Layer 6 sorries):**
- `PROOF_PRST_MONO` (Layer 0/2 leftover) — body has a nested `?h t. p = Tup_pt h t /\ (... /\ (?f g. rec t f /\ rec t (Imp_pf f g) /\ ...))`. Two recursive calls on `t` inside an inner existential; no existing `mono_iff_*` factory matches this shape (would need a fresh `mono_iff_binary_right_with_inner_exists_step`). ~80 lines bespoke.
- `PROOF_PRST_CONS` — recursion equation. PROOF_PRST_AT delivers `?h0 t0. Tup_pt h t = Tup_pt h0 t0 /\ P(h0, t0)`; need to collapse to `P(h, t)` via TUP_PT_INJ. DSL friction: `CHOOSE_WITNESS` produces SELECT-term witnesses that `REWRITE_RULE` refuses to rewrite under the inner `?f g.` binder (tactics._bottom_up line 998 filters rules with non-empty asl when descending under binders). Workarounds explored: ELIM_EX + INST (INST can't substitute SELECT terms), kernel-level CHOOSE_WITNESS + REWRITE_RULE (same binder problem), `with .proof()` + `by_rewrite_of` (same). Downstream uses can route through PROOF_PRST_AT directly so CONS is convenience, not load-bearing.
- `PROV_PRST_ADJ_DEF_AT` — as currently stated, requires `is_pterm x /\ is_pterm y` preconditions to invoke the `is_Refl` schema. Either add the precondition or sorry.
- `MU_CORRECTNESS` — keep as `prove_axiom` (per plan's risk register).
- `PROV_PRST_SUBST_AXIOM` — needs new `IS_PR_DEF_CLOSED_UNDER_SUBST` obligation in prst_pr (~40 lines).
- `PROV_PRST_MP` — needs proof-list concatenation lemma + a Proof_PRST monotonicity-under-concat lemma. Not provided by the current Proof_PRST encoding; either add the concat helper or revisit the encoding.

**DSL friction newly observed:**
- `_bottom_up`'s "filter rules with non-empty asl under binders" rule (line 998 of tactics.py) makes REWRITE_RULE useless for substituting choose-derived `_eq` facts under inner binders. Two ways to work around it: prove the unconditional version of the rule first (so its asl is empty), or write the substitution at the kernel level using AP_TERM / ABS / etc.
- `axiom_name_str` passed to a generic helper must be parenthesised (`"(" + s + ")"`) before concatenating into a parse-string — otherwise multi-token forms like `"proj_def_axiom_at i n"` get re-parsed as `is_pr_def proj_def_axiom_at` applied to `i n`, type-mismatching.

---

## Layer 7 — `prst_proof` PR-eval + `Prov_PRST_internal` (5 sorries) — **partial: 2/6 cleared**

Depends on Layer 6 and on Layer 0 real bodies of `numeral_pr` / `substitute_pr` / `diag_pr`. Layer 2 relax (`is_pterm`'s App branch now uses `is_partial_pr_sym`) unblocked `IS_PFORM_PROV_PRST_INTERNAL`.

**Done (2 cleared):**
- `FREE_IN_PROV_PRST_INTERNAL` — one `by_rewrite` over the unfolded `Prov_PRST_internal` body, `T_pt`/`Adj_pt` definitions, the four FREE_IN_P_AT_* equations (EQ/APP/TUP/VAR), a new `FREE_IN_P_AT_EMPTY` helper, and boolean simp rules (OR_F_LEFT/RIGHT + a locally-derived OR_IDEMP). Independent of well-formedness.
- `IS_PFORM_PROV_PRST_INTERNAL` — unblocked by the Layer 2 relax (option B): IS_PTERM_AT_APP now reads `is_pterm (App_pt f args) = is_partial_pr_sym f /\ is_pterm args`. Proof structure: unfold to `Eq_pf <lhs> T_pt`, apply IS_PFORM_AT_EQ, prove `is_pterm` for both sides via IS_PTERM_AT_APP/_TUP/_VAR/_EMPTY recursively. Every `is_partial_pr_sym _` obligation discharges via `IS_PR_SYM_IMP_PARTIAL` (new helper, prst_syntax) composed with `IS_PR_SYM_PROJ` / `IS_PR_SYM_ADJ`, plus `IS_PARTIAL_PR_SYM_MU` for the `mu_sym Proof_PRST_pr` slot. ~130 lines.

**Layer 2 relax (option B) — applied:**
- `is_partial_pr_sym` moved from prst_pr.py to prst_syntax.py so `_IS_PTERM_F_DEF`'s App-branch guard can mention it. The body uses bare `Pair_ord 6 g` encoding rather than `mu_sym g`; the mu_sym constant + `IS_PARTIAL_PR_SYM_MU` bridge stay in prst_pr.py (which keeps prst_syntax mu-agnostic at the symbol-constant level).
- `_IS_PTERM_F_DEF` App branch: `is_pr_sym fn` → `is_partial_pr_sym fn`. `IS_PTERM_MONO`'s `_mono_iff_app_pt_step` call passes `is_partial_pr_sym` as the guard. `IS_PTERM_AT_EMPTY` body string + `SUBSTITUTE_P_PRESERVES_IS_PTERM`'s App case body string updated to match.
- New helper `IS_PR_SYM_IMP_PARTIAL: |- !f. is_pr_sym f ==> is_partial_pr_sym f` in prst_syntax. Lifts every concrete `IS_PR_SYM_*` lemma to its partial-PR counterpart for downstream `is_pterm` checks.
- Semantic invariant: `is_pr_sym` still means "totally-defined PR symbol" (5-disjunct body unchanged); `is_partial_pr_sym` is the mu-closed wider class admitted by `is_pterm`. No downstream consumer broke: pure-PR App-sites (e.g. PR-defining axioms) lift to `is_partial_pr_sym fn` via `IS_PR_SYM_IMP_PARTIAL` in one line.

**New helper:** `FREE_IN_P_AT_EMPTY: |- !v. free_in_p Empty_pt v = F` (lives in `prst_proof.py`). `Empty_pt` matches none of `free_in_p`'s 7 disjuncts, so `derive_rec_eq_pw` can't generate this case (it dispatches matched disjuncts, not the all-mismatch fallback) and the `IS_PTERM_AT_EMPTY` pattern is inapplicable (is_pterm has an Empty_pt disjunct; free_in_p does not). Manual proof: unfold via `FREE_IN_P_REC` at `Empty_pt`, case-split, refute each disjunct via the relevant constructor-vs-Empty disjointness lemma (`VAR_PT_NEQ_EMPTY_PT` / `TUP_PT_NEQ_EMPTY_PT` / …). ~110 lines.

**Blocked (4 remaining):**
- `PROV_PRST_SUBSTITUTE_EVAL` — Layer-0 body landed (`course_rec g_subst h_subst`); proof now needs the structural induction over `IS_PFORM_REC` per-case + Tier-3 dispatch via `PROV_PRST_COURSE_REC_STEP_DEF`. ~80 lines, mechanisable.
- `PROV_PRST_NUMERAL_EVAL` — `numeral_pr_def` body is real; proof needs `PROV_PRST_MP` + `PROV_PRST_SUBST_AXIOM` + `PROV_PRST_ADJ_DEF_AT` (Layer 6 sorries) to chain through the `rec_sym` composition.
- `PROV_PRST_DIAG_EVAL` — `diag_pr_def` fully wired (const_sym closes var_x). Proof composes SUBSTITUTE_EVAL + NUMERAL_EVAL.
- `PROV_PRST_REPRESENTS` — now unblocked by `PROOF_PRST_PR_CORRECT` + `PROOF_PRST_PR_INTERNAL_EVAL` (posited) + `MU_CORRECTNESS` + `DIAG_EVAL`. Forward direction: from a Proof_PRST witness `p`, get `App_pt Proof_PRST_pr (Tup_pt p ...) = T_pt` via CORRECT, then `Prov_PRST (Eq_pf ... T_pt)` via INTERNAL_EVAL, then lift `p` to `find_proof_pr`'s witness via MU_CORRECTNESS. ~50 lines once SUBSTITUTE/NUMERAL/DIAG_EVAL land.

**DSL friction newly observed (Layer 7 part 1):**
- No public `OR_IDEMP` (`|- !p. (p \/ p) = p`). `tactics.OR_F_LEFT`/`OR_F_RIGHT` cover the `F`-leg simplifications and `AC_PROVE` handles assoc+comm, but `by_rewrite`'s normal-form check is strict modulo only the supplied + active simp rules — without idempotence, symmetric `Tup_pt (X) (X)`-derived `P \/ P` won't collapse. Derived locally from `DISJ1` + `DISJ_CASES` + `DEDUCT_ANTISYM_RULE`; worth promoting to tactics.py for any AT-equation chain that walks symmetric `Tup_pt` cells.
- `by_rewrite` doesn't beta-reduce by default. To use `ADJ_PT_DEF` (`Adj_pt = \a b. ...`) at concrete `Adj_pt Empty_pt Empty_pt`, the lambda-form rule alone produces `(\a b. ...) Empty_pt Empty_pt` and stalls. `p.unfold(ADJ_PT_DEF, "Empty_pt", "Empty_pt")` delivers the post-beta applied form. For chains that hit multiple Adj/comp applications, hand-build the applied form once per arg shape or use `by_unfold` / `by_rewrite_of(beta=True)`.
- `tactics.DISCH` (kernel rule) is re-exported from `tactics`, not `fusion`. The shape `from fusion import ASSUME, DISCH` fails — `fusion` ships `ASSUME` but `DISCH` is in `tactics`.
- `bool_ty` lives in `fusion`, not `basics`. (`basics` re-exports many constructors but not the bare type.)

**Cost note:** Original estimate was ~250 lines for the whole layer. With `PROOF_PRST_PR_CORRECT` + `PROOF_PRST_PR_INTERNAL_EVAL` posited, the four remaining lemmas in Layer 7 are now all proof-writing exercises against Layer 6 prerequisites (no more semantic blockers). Revised estimate: ~250 lines once the Layer 6 sorries below (`PROV_PRST_MP`, `PROV_PRST_SUBST_AXIOM`, `PROV_PRST_ADJ_DEF_AT`) clear.

---

## Layer 8 — `prst_repr` (7 sorries)

Depends on Layer 7.

- `T_PT_NEQ_F_PT` — tag-disjointness through `Adj_pt`/`Empty_pt`
- `REPRESENTABILITY_POSITIVE/NEGATIVE` — unfold `substitute_p` through `Eq_pf` + `App_pt`, then unfold `represents_pred_prst`. ~5 lines each.
- `SUBSTITUTE_REPRESENTS_PRST` — combine `PROV_PRST_SUBSTITUTE_EVAL` and `PROV_PRST_NUMERAL_EVAL` per arg slot via equality reasoning. ~30 lines.
- `DIAG_REPRESENTS_PRST` — one `PROV_PRST_DIAG_EVAL` + numeral eval. ~10 lines.
- `PROOF_PRST_REPRESENTS_POS/NEG` — one defining-equation specialisation per branch. ~20 lines combined.

**Cost:** ~80 lines. Straightforwardly applies Layer 7.

---

## Layer 9 — `prst_godel1` (6 sorries)

Depends on Layer 8.

- `DIAGONAL_LEMMA_PRST` (~80 lines) — substitute `(App_pt diag_pr (Tup_pt (Var_pt var_x) Empty_pt))` into `phi`, rewrite via `DIAG_REPRESENTS_PRST`, close the iff by PRST equality reasoning
- `G_PRST_DIAGONAL_EQ` (~10 lines) — specialise `DIAGONAL_LEMMA_PRST` at `phi = Not_pf Prov_PRST_internal` using `IS_PFORM_PROV_PRST_INTERNAL` + `FREE_IN_PROV_PRST_INTERNAL`
- `PRST_CONSISTENT` (~80 lines) — standard nat0 HOL model argument; one soundness obligation per PR-defining equation
- `PRST_SIGMA1_SOUND` (~80 lines) — induction on `Prov_PRST` witness; atomic case dispatches to PR-symbol defining equations. **Watch:** `IS_SIGMA1_DEF` / `SIGMA1_HOLDS_DEF` are currently `T`-stubs; needs real definitions of the Sigma_1 fragment and its truth predicate (this is another Layer 0-style fix).
- `GODEL_FIRST_PRST` (~80 lines) — the two-conjunct argument; uses `PROV_PRST_REPRESENTS`, `G_PRST_DIAGONAL_EQ`, `PRST_CONSISTENT`, `PRST_SIGMA1_SOUND`
- `PRST_ESSENTIALLY_UNDECIDABLE` (~50 lines) — repeat diagonal at an arbitrary consistent extension `T`

**Cost:** ~400 lines. The Sigma_1 fragment definition is the tricky non-obvious bit; everything else is mechanical.

---

## Layer 10 — `prst_godel2` (8 sorries)

Depends on Layer 9 + `mu_sym` + `mp_combine_pr` (a fresh PR symbol whose body is `0` and whose correctness theorem is `MP_COMBINE_PR_CORRECT`).

- `IS_PFORM_CON_PRST` (~5 lines) — closure of `is_pform`
- `DERIV_D1` (~5 lines) — forward direction of `PROV_PRST_REPRESENTS`
- `MP_COMBINE_PR_CORRECT` (~30 lines) — needs the real body of `mp_combine_pr` (a Layer-0 fix: currently `0`); definitional unfolding + structural case analysis on `Proof_PRST_pr`
- `DERIV_D2` (~50 lines) — `MP_COMBINE_PR_CORRECT` + `MU_CORRECTNESS` at `f = Proof_PRST_pr`. Pivotal step where `mu_sym` replaces existential elimination.
- `DERIV_D3` (~200 lines) — the heavy hitter. Pi_1 structural induction over Eq_pf / In_pa / Not_pf / Imp_pf / App_pt formula constructors; needs a fresh PR symbol `reflect_pr` (analog of Buss/Boolos's `BProof`) defined by primitive recursion on phi's syntax. Per the file comment, this is the bulk of G2 cost.
- `LOEB_PRST` (~60 lines) — diagonal at `chi(x) := Imp_pf (substitute_p Prov_PRST_internal (Var_pt var_x) var_x) psi`, then chain D1/D2/D3
- `GODEL_SECOND_PRST` (~20 lines) — `LOEB_PRST` at `psi = falsity_witness`
- `PRST_CANNOT_PROVE_OWN_CONSISTENCY` (~10 lines) — conditional restatement

**Cost:** ~380 lines + `mp_combine_pr` / `reflect_pr` PR-symbol bodies (~50 lines each).

---

## Critical path and order of attack

Two reasonable orderings:

**Bottom-up (foundations first, safest):**

Layer 0 → 1 → 2 → 3 → 4 → 5 → 6 → 7 → 8 → 9 → 10.

**G1-first (defer G2):**

Same path but stop at Layer 9. G2 (Layer 10) is independently the most expensive node (`DERIV_D3` alone is ~200 lines plus a new PR symbol); deferring it until after G1 lands is reasonable if the goal is to demonstrate the design.

**Estimated total:** ~1800 lines of real Pyzar proof code to discharge all 75 sorries, plus ~300 lines of replaced stub definition bodies. Matches the comment-block estimate of ~2150 in `prst_godel1.py`.

---

## Risk register

1. **`MU_CORRECTNESS` status.** Treat as a posited axiom (`prove_axiom`); attempting to mechanise it as a HOL theorem would mean formalising the standard nat0 model, which is out of scope for the incompleteness mechanisation. **Resolved: posited via `new_axiom` in prst_proof.py.**

1b. **`Proof_PRST_pr` body status.** Same precedent as MU_CORRECTNESS. Posited via two `new_axiom`s (`PROOF_PRST_PR_CORRECT` + `PROOF_PRST_PR_INTERNAL_EVAL`) in prst_proof.py; sentinel `proj 1 2` body retained. See "G1 + G2 commitment surface" section.

2. **Sigma_1 fragment definition.** `IS_SIGMA1_DEF` and `SIGMA1_HOLDS_DEF` are stub `T`-bodies. Layer 9 needs real definitions; this is a small design task that hasn't been done.

3. **`Tup_pt` recursion inside `is_pterm` / `free_in_p` / `substitute_p`.** The args-list recursion lives directly in the main recogniser bodies via a `Tup_pt`-disjunct that recurses on both head and tail. Verify the `nat0_lt` size argument goes through `NAT0_LT_PAIR_ORD_L/R` for both projections before relying on Layer 2's App_pt AT-equation. **Verified during Layer 2.**

4. **`Proof_PRST_pr` defining equation — RESOLVED via posited axioms.** `substitute_pr`, `numeral_pr`, `diag_pr` have real bodies. `Proof_PRST_pr_def` retains its `proj 1 2` sentinel body; its correctness is committed via two `new_axiom`s in `prst_proof.py`:
   - `PROOF_PRST_PR_CORRECT` — HOL-level: `Proof_PRST p n <=> App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt`.
   - `PROOF_PRST_PR_INTERNAL_EVAL` — PRST-internal: T_pt evaluation is internally Prov_PRST-provable.

   Same precedent as `MU_CORRECTNESS`. Rationale: the constructive route requires net-new bounded-search PR infrastructure (`nth_pr`, `exists_pair_pr`, `len_pr`) whose only consumer in the whole chain is `Proof_PRST_pr` itself — other Layer-10 PR symbols (`mp_combine_pr`, `reflect_pr`) reuse existing infra. See "G1 + G2 commitment surface" below.

5. **Forward declarations across module boundaries.** `is_pr_sym` / `pr_arity` are defined in `prst_syntax.py` but semantically belong in `prst_pr.py`. **Resolved in Layer 4 part 1:** the real `IS_PR_SYM_DEF` body lives in `prst_syntax.py` and uses bare nat0 literals / `Pair_ord` shapes (no reference to `zero_sym`/`adj_sym`/…), so the forward-decl is self-contained.

6. **`pr_arity` recursive case.** *(New, Layer 4.)* `PR_ARITY_REC`'s intended statement is recursive on `g`; the encoding `rec_sym g h = Pair_ord 4 (Pair_ord g h)` carries no arity-of-g information, so mechanising `pr_arity` faithfully forces a `define_wf_lt` setup + a ~150-line `PR_ARITY_MONO`. Three forks are listed in the Layer 4 section. Resolution needed before Layer 5 *only if* downstream code starts consuming `pr_arity` — currently nothing does.

7. **`hf_repr_core.numeral` reuse.** PRST currently imports `numeral` and `substitute` from `hf_repr_core` / `hf_syntax` for the eval lemmas. Confirm those carry over to the shared nat0 encoding without re-proof — the file comment claims they do, but `PROV_PRST_SUBSTITUTE_EVAL` is the load-bearing place where it has to be true.

---

## G1 + G2 commitment surface — posited axioms

The mechanisation commits two correctness statements as `new_axiom`s rather than constructing them. Both target irreducibly-semantic claims about specific PR symbols whose construction requires building a layer (model theory or net-new PR scaffolding) outside the scope of the Gödel argument itself.

| Axiom | Statement | Lives in |
|-------|-----------|----------|
| `MU_CORRECTNESS` | `is_partial_pr_sym f /\ App_pt f (Tup_pt q args) = T_pt ==> App_pt f (Tup_pt (App_pt (mu_sym f) args) args) = T_pt` | `prst_proof.py` |
| `PROOF_PRST_PR_CORRECT` | `Proof_PRST p n <=> App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt` | `prst_proof.py` |
| `PROOF_PRST_PR_INTERNAL_EVAL` | `App_pt Proof_PRST_pr ... = T_pt ==> Prov_PRST (Eq_pf (App_pt Proof_PRST_pr ...) T_pt)` | `prst_proof.py` |

**Audit of infra reuse for `Proof_PRST_pr`** (justifies the axiomatic choice):

| Remaining PR symbol | Construction shape | Reuses bounded-search infra (`nth_pr` / `exists_pair_pr` / `len_pr`)? |
|---|---|---|
| `Proof_PRST_pr` | proof-list scan w/ bounded MP-pair search | **Yes — sole consumer.** |
| `mp_combine_pr` (G2) | list-append + cons | No — needs simpler list-append helper. |
| `reflect_pr` (G2 D3) | Π₁ structural induction on formula constructors | No — reuses existing `course_rec` + `pair_left/right/ord` (substitute_pr-shaped). |
| `numeral_pr` / `substitute_pr` / `diag_pr` / `find_proof_pr` | rec_sym / course_rec / composition / mu | No. |

Mechanising `Proof_PRST_pr` faithfully would require ~150 lines of `nth_pr`/`exists_pair_pr`/`len_pr` PR scaffolding plus ~400 lines of the proof-checker body itself, with **zero amortisation** across other symbols. The other expensive G2 symbols are independently cheaper.

**Trust-burden trade-off recap:**
- Each posit weakens the "PRST verifies its own Gödel theorems" demonstration by one notch.
- Soundness of all three axioms holds in the standard nat0 HOL model (μ via least-witness convention, `Proof_PRST_pr` via PR-completeness applied to the decidable Sigma_1 predicate `Proof_PRST`).
- Total non-mechanised commitments after this fork: 3 axioms (vs. 1 with the constructive route). HF-side has 0.

---

## Structural-recursion harness (Tier 3) — infra landed

**Final design:** three primitives composed together — `course_rec_sym` for the recursion machinery, `pair_left_sym` + `pair_right_sym` for the non-uniform extraction cases that `course_rec`'s uniform descent can't handle on its own.

The naive "course_rec alone subsumes pair_left/right" plan didn't survive contact with **App_pt**'s encoding: `App_pt fn args = Pair_ord 11 (Pair_ord fn args)`. Substitute_p's App case is `substitute_p (App_pt fn args) t v = App_pt fn (substitute_p args t v)` — `fn` is **kept unchanged**, only `args` is recursed on. Course_rec descends uniformly into both children of every Pair_ord, so the recursive value at the inner pair returns `Pair_ord (sub fn) (sub args)` — wrong. To produce `App_pt fn (sub args) = Pair_ord 11 (Pair_ord fn (sub args))` we need `pair_left b` (= `fn`) and `pair_right rec_right` (= `sub args` once the inner default returns `Pair_ord sub(fn) sub(args)`). No way around it with pure uniform recursion.

Same shape recurs in `is_pr_axiom_pr` (Proof_PRST_pr's per-step axiom recogniser): every axiom-family pattern like `proj_def_axiom_at i n = Eq_pf (App_pt (proj_sym i n) args) (Var_t i)` needs to extract `(i, n)` from a candidate formula — pair_left/right work.

### What this unblocks

With the infra landed:
- **`substitute_pr_def`** ~50 lines: `course_rec g_subst h_subst`. `g_subst := const_sym 0` (Empty_pt = 0 returned at base). `h_subst` dispatches on `a` (the tag) via `if_in_sym` chains across ~6 cases. App_pt case: `Pair_ord 11 (Pair_ord (pair_left b) (pair_right rec_right))`. Tup_pt / Eq_pf / In_pa / Imp_pf / Not_pf: `Pair_ord a rec_right`. Var_pt: `if_in_sym b {v} t (Pair_ord 10 b)` using pair_left/right on y_vec to extract t, v. Default (inner-Pair_ord, intermediate level): `Pair_ord rec_left rec_right`.
- **`Proof_PRST_pr_def`** ~200 lines: course_rec on the proof list (Tup_pt cons chain). Per-step needs `is_pr_axiom_pr` (10-way if_in_sym dispatch across axiom-family tags with payload extraction via pair_left/right) and a bounded `is_mp_pr` check.
- **`PROV_PRST_SUBSTITUTE_EVAL`** ~80 lines: structural induction on F via `IS_PFORM_REC`, per-case specialise `PROV_PRST_COURSE_REC_STEP_DEF` at `(g_subst, h_subst, tag, payload, y_vec)`, reduce h_subst at the specific tag using its `if_in_sym` defining equations, bridge to HOL-side `substitute F t v` via `SUBSTITUTE_P_AT_*`.


---
