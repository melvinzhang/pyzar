# PRST `p.sorry()` plan of attack

Census across `prst_*.py` (75 sorries total):

| File | sorries | Role |
|------|---------|------|
| `prst_syntax.py` | 19 | App_pt constructor + extended `is_pterm`/`is_pform`/`free_in_p`/`substitute_p` AT-equations and preservation lemmas |
| `prst_connectives.py` | 3 | `substitute_p` distribution over And/Or/Iff (alias-thin wrappers) |
| `prst_pr.py` | 17 | PR-symbol registry (`is_pr_sym`, `pr_arity`) + base-layer defining-equation axioms + `is_pr_def` recogniser + mu-closure registry |
| `prst_proof.py` | 15 | `Proof_PRST` / `Prov_PRST` + closure rules + per-axiom `PROV_PRST_*_DEF` corollaries + `MU_CORRECTNESS` + PR-eval lemmas + `Prov_PRST_internal` |
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
  - `substitute_pr_def` / `Proof_PRST_pr_def` — placeholder PR compositions (`proj_sym 0 3` / `proj_sym 1 2`); full bodies are ~100 / ~50-symbol-composition chains that Layer 7 / Layer 10 fill in alongside `PROV_PRST_SUBSTITUTE_EVAL` / `PROOF_PRST_PR_DEFINING`. Downstream lemmas remain sorry'd against these placeholders, so the placeholder choice doesn't propagate
  - `diag_pr_def` — partial composition (numeral_pr leg wired; var_x leg is a structural hole pending a `const_sym` primitive)
- `prst_proof.py`: **DONE.**
  - `Proof_PRST_def` — converted to `define_wf_lt` recursion on the proof list with sorry'd MONO. AT-equations `PROOF_PRST_NIL` / `PROOF_PRST_CONS` are derivable from the wf-lt recursion equation (Layer 6 work)

These are not `p.sorry()` calls, but every downstream AT-equation that "unfolds" them silently relies on real bodies. Replace them **before** attempting the AT proofs, otherwise the AT lemma will be unprovable (constant stubs don't satisfy the recursion equations).

---

## Layer 1 — `prst_syntax` constructor lemmas (4 sorries)

Free-standing; no dependencies beyond `hf_syntax`'s `Pair_ord` / `nat0_lt` machinery.

- `NAT0_LT_APP_PT_L`, `NAT0_LT_APP_PT_R` — one or two `NAT0_LT_PAIR_ORD_L/R` + `NAT0_LT_TRANS` each
- `APP_PT_INJ` — two `PAIR_ORD_INJ` invocations
- `APP_PT_DISJOINT_VAR_T`, `APP_PT_DISJOINT_EMPTY` — tag-disjointness (SUC0^11 0 ≠ SUC0^2 0 ≠ 0)

**Cost:** ~50 lines. Pattern is identical to existing `hf_syntax` constructor lemmas; copy-paste-adapt.

---

## Layer 2 — `prst_syntax` recogniser AT-equations (15 sorries)

Depends on Layer 0 real bodies + Layer 1 size lemmas.

- `IS_PTERM_AT_EMPTY` / `_VAR` / `_APP` (3)
- `IS_PFORM_AT_EQ` / `_IN` / `_NOT` / `_IMP` (4)
- `FREE_IN_P_AT_VAR` / `_APP` (2)
- `SUBSTITUTE_P_AT_VAR_HIT` / `_VAR_MISS` / `_APP` (3)
- `SUBSTITUTE_P_PRESERVES_IS_PTERM`, `SUBSTITUTE_P_PRESERVES_IS_PFORM` (2)

**Cost:** ~250 lines. Each AT is one unfold of the recursion body via `define_with_at` machinery plus tag-disjointness; preservation lemmas are induction over `nat0_lt`.

⚠️ Watch the `App_pt` cases: the recursion call goes through the args slot directly (justified by `NAT0_LT_APP_PT_R`), with the binary `Tup_pt` cons cell unfolded inside `is_pterm` / `free_in_p` / `substitute_p` themselves.

---

## Layer 3 — `prst_connectives` (3 sorries)

- `SUBSTITUTE_P_AT_AND` / `_AT_OR` / `_AT_IFF`

**Cost:** ~30 lines total. Each one: unfold the connective via `*_F_AT`, apply `SUBSTITUTE_P_AT_NOT` / `_IMP` (Layer 2). These are pure aliases of the `hf_connectives` versions on the shared encoding — the only reason they need restating is so consumers can parse-name `substitute_p` instead of `substitute`.

---

## Layer 4 — `prst_pr` PR-symbol registry (10 sorries)

Depends on Layer 0 real bodies of `IS_PR_SYM_DEF` / `PR_ARITY_DEF`.

- `IS_PR_SYM_ZERO/ADJ/PROJ/IF_IN/REC` (5)
- `PR_ARITY_ZERO/ADJ/PROJ/IF_IN/REC` (5)

**Cost:** ~80 lines. Each lemma is one `define_with_at` unfold of the registry body + `Pair_ord` injectivity to distinguish tags. The hard part is choosing the registry body shape so that all five tag-cases are decidable.

---

## Layer 5 — `prst_pr` `is_pr_def` recogniser (6 sorries)

Depends on Layer 0 real `IS_PR_DEF_DEF` body + the per-axiom closed nat0s being real (Layer 0 `PROJ_DEF_AXIOM_AT_DEF` etc.) + Layer 4.

- `IS_PR_DEF_HOLDS_ZERO/PROJ/IF_IN_TRUE/IF_IN_FALSE/REC_BASE/REC_STEP` (6)
- `IS_PARTIAL_PR_SYM_MU` (1)

**Cost:** ~60 lines. Each: one DISJ-introduction into the `is_pr_def` body, then EXISTS at the parameter slots (PROJ/REC cases). The mu lemma is one unfold of the `is_partial_pr_sym` recursion.

⚠️ Critical Layer 0 dependency: `IS_PR_DEF_DEF`'s real body (the 6-disjunct in the comment) must precede this layer, otherwise `IS_PR_DEF_HOLDS_ZERO` is provably false (current body is `F`).

---

## Layer 6 — `prst_proof` foundations (8 sorries)

Depends on Layer 0 real `Proof_PRST_def` body + Layers 1-5.

- `PROOF_PRST_NIL`, `PROOF_PRST_CONS` (2) — `define_wf_lt` unfolds
- `PROV_PRST_AXIOM`, `PROV_PRST_MP` (2) — exhibit one-line / append-with-MP proofs and EXISTS
- `PROV_PRST_SUBST_AXIOM` (1) — requires a closure lemma `is_pr_def F ==> is_pr_def (substitute_p F t v)`, which is a fresh proof obligation not yet stated (add it under `prst_pr` as `IS_PR_DEF_CLOSED_UNDER_SUBST`; ~40 lines via the disjunct structure)
- `MU_CORRECTNESS` (1) — sole non-PR axiom; either kept as `p.sorry()` and treated as an axiom posit, **or** posited via `prove_axiom` machinery; the standard nat0 HOL model justifies it but the proof is not internal to the kernel
- The per-axiom `PROV_PRST_ZERO_DEF/PROJ_DEF/IF_IN_TRUE_DEF/IF_IN_FALSE_DEF/REC_BASE_DEF/REC_STEP_DEF` (6) + `PROV_PRST_ADJ_DEF_AT` (1) — each is MP of `PROV_PRST_AXIOM` against the corresponding `IS_PR_DEF_HOLDS_*`. Per the file comment, these "fall out of MP + IS_PR_DEF_HOLDS_*"; should be ~3 lines each once the chain is in place.

**Cost:** ~150 lines + the new `IS_PR_DEF_CLOSED_UNDER_SUBST` (~40 lines).

⚠️ Decide upfront whether `MU_CORRECTNESS` is an **axiom** (cleanest, matches the design intent in the comment) or a **theorem in a fixed HOL model** (cheapest mechanisation). The file's narrative treats it as the lone axiom about `mu_sym`; recommend keeping it as `prove_axiom`.

---

## Layer 7 — `prst_proof` PR-eval + `Prov_PRST_internal` (5 sorries)

Depends on Layer 6 and on Layer 0 real bodies of `numeral_pr` / `substitute_pr` / `diag_pr`.

- `PROV_PRST_SUBSTITUTE_EVAL` — structural induction on `F` through five constructor cases; each case is one `PRST_REC_STEP` instance against `substitute_pr`'s defining equations
- `PROV_PRST_NUMERAL_EVAL` — induction on `n`
- `PROV_PRST_DIAG_EVAL` — composition of the previous two via `DIAG_PR_DEFINING`
- `IS_PFORM_PROV_PRST_INTERNAL` — closure of `is_pform` under `Eq_pf` / `App_pt` (Layer 2)
- `FREE_IN_PROV_PRST_INTERNAL` — same, for `free_in_p`
- `PROV_PRST_REPRESENTS` — the headline representability theorem; ~80 lines per the file comment, both directions of the iff.

**Cost:** ~250 lines. This is where the PR-symbol-as-term design pays off: every "eval" lemma is a `PROV_PRST_REC_STEP`-driven walk, no trace sets.

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

1. **`MU_CORRECTNESS` status.** Treat as a posited axiom (`prove_axiom`); attempting to mechanise it as a HOL theorem would mean formalising the standard nat0 model, which is out of scope for the incompleteness mechanisation. Decision needed *before* Layer 6.

2. **Sigma_1 fragment definition.** `IS_SIGMA1_DEF` and `SIGMA1_HOLDS_DEF` are stub `T`-bodies. Layer 9 needs real definitions; this is a small design task that hasn't been done.

3. **`Tup_pt` recursion inside `is_pterm` / `free_in_p` / `substitute_p`.** The args-list recursion lives directly in the main recogniser bodies via a `Tup_pt`-disjunct that recurses on both head and tail. Verify the `nat0_lt` size argument goes through `NAT0_LT_PAIR_ORD_L/R` for both projections before relying on Layer 2's App_pt AT-equation.

4. **`substitute_pr` / `numeral_pr` / `diag_pr` / `Proof_PRST_pr` defining equations.** Currently all `0`. Their real bodies are base-layer compositions; building them is a substantial chunk of Layer 0 (~200 lines on its own).

5. **Forward declarations across module boundaries.** `is_pr_sym` / `pr_arity` are defined in `prst_syntax.py` but semantically belong in `prst_pr.py`. Confirm the parser is happy with the redefinition pattern before committing to Layer 4 proofs.

6. **`hf_repr_core.numeral` reuse.** PRST currently imports `numeral` and `substitute` from `hf_repr_core` / `hf_syntax` for the eval lemmas. Confirm those carry over to the shared nat0 encoding without re-proof — the file comment claims they do, but `PROV_PRST_SUBSTITUTE_EVAL` is the load-bearing place where it has to be true.

---

## Recommended first commit

Land Layer 0 + Layer 1 + Layer 3 together — they unblock Layer 2 (the largest leaf layer) and Layer 4 (the registry), and are individually small enough to review in one pass. ~150 lines of real proofs + ~150 lines of replaced definition bodies. After that, Layer 2 is a single dedicated commit (~250 lines).
