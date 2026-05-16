# PRST Remaining `p.sorry()` Ledger

This file intentionally lists only open `p.sorry()` obligations in
`prst_*.py`. Completed layer notes are removed.

The sole explicit PRST axiom outside this ledger is `MU_CORRECTNESS`.

## Order of Attack

This ledger is ordered by dependency and expected discharge path, not by file.
Pure forwarding theorems are deleted instead of tracked.

### Architectural note: Paulson-form structural bridge

`Mem_PRST`, `ValidProof_PRST`, and `Proof_PRST` remain as HOL relations
for stating top-level theorems (Gödel statements mention `Prov_PRST`,
which is defined via `Proof_PRST`). The bridge to the PR checker
`Proof_PRST_pr` is the single theorem `PROOF_PRST_PR_REPRESENTS`:

```
|- !pf n.
     (Proof_PRST pf n
       ==> App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = T_pt)
  /\ (~Proof_PRST pf n
       ==> App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = F_pt).
```

Internal checker sub-lemmas (`mem_t_pr`, `exists_mp_witness_pr`,
`valid_step_pr`, `valid_proof_list_pr`, `is_tup_pr`, `is_pterm_pr`,
`is_pr_axiom_pr`) are proof-internal to `PROOF_PRST_PR_REPRESENTS` and
do not appear as separate stubs; they re-emerge as sub-lemmas during
its discharge. This replaces the previously-cut granular section 0 +
0a stack (`IS_TUP_PR_CORRECT`, `MEM_T_PR_CORRECT`,
`EXISTS_MP_WITNESS_PR_CORRECT`, `VALID_STEP_PR_CORRECT`,
`VALID_PROOF_LIST_PR_CORRECT`, `PROOF_PRST_PR_BODY_CORRECT`, and the
`APP_PT_*` evaluator stack) with one Paulson-form bridge.

Boolean-view consumers (`= T_pt \/ = F_pt` dichotomy, semantic
negation, quoted-input lifts) instantiate the bridge inline at the
call site rather than going through named corollary stubs. The
Prov_PRST-flavoured ones compose the bridge with `PROV_PRST_PR_EVAL`
at `r := T_pt` / `r := F_pt`.

### 1. `Proof_PRST_pr` Checker API Boundary

Two unifying Paulson-form stubs cover the checker API. Per-pattern
corollaries (boolean-value dichotomy, semantic negation, quoted-input
forms, T_pt/F_pt specialisations) are not stubbed as named theorems;
downstream consumers instantiate the unifiers inline at the call
site. If a pattern recurs enough that a named lemma earns its keep,
introduce it then as a real (non-sorry) theorem.

Structural bridge:

- `PROOF_PRST_PR_REPRESENTS` — `Proof_PRST pf n` iff
  `App_pt Proof_PRST_pr ... = T_pt` (with the negative direction
  giving `F_pt`). Stated as a paired implication so the same theorem
  supplies both directions used by downstream consumers (boolean
  dichotomy by LEM on `Proof_PRST pf n`; semantic negation directly;
  quoted-input forms by composing with `PROV_PRST_PR_EVAL` plus
  `quote_hf`).

Generic PR-eval bridge:

- `PROV_PRST_PR_EVAL` —
  `is_partial_pr_sym f /\ App_pt f args = r
   ==> Prov_PRST (Eq_pf (App_pt f args) r)`.
  Paulson-form bridge proved by induction over the µ-closure
  structure of `is_partial_pr_sym`, using
  `PROV_PRST_PR_DEF_AT_LIFT` (§3a) at the base case and
  `MU_CORRECTNESS` for the µ-closure step. Boolean-target uses
  instantiate `r := T_pt` / `r := F_pt` at the call site. Per-symbol
  uses (substitute_pr / numeral_pr / diag_pr) instantiate `f` and `r`
  similarly; see §3 evaluator clauses.

The quoted-input obligations downstream intentionally do not assert
raw-to-`quote_hf` checker-value preservation. `quote_hf` is the
object-language numeral interface; the proof route uses
`numeral_pr`/`quote_hf` evaluation plus internalisation of the
resulting PR computation.

### 2. Proof-List Combination API

These discharge the remaining list plumbing used by PRST modus ponens and the
G2 proof-combinator path.

- `MP_COMBINE_PR_CORRECT`

### 3. Public PR-Symbol Evaluators

The public evaluators are each a one-statement bundled obligation
specialising `PROV_PRST_PR_EVAL` (§1) at a specific PR symbol. The
previously-stubbed 15-clause decomposition (10 substitute
constructor clauses + 1 substitute combinator + 2 numeral + 2 diag)
has been consolidated: each evaluator captures both its HOL-side
structural correctness (is_partial_pr_sym + universal App_pt
equation) and the PR_EVAL lift in a single sorry.

- `PROV_PRST_SUBSTITUTE_EVAL` — substitute_pr at any (F, t, v).
- `PROV_PRST_NUMERAL_EVAL` — numeral_pr equals quote_hf.
- `PROV_PRST_DIAG_EVAL` — diag_pr equals the meta-level diag.

Discharge route for each: (1) is_partial_pr_sym <symbol> by
structural argument over the symbol's comp / rec / course_rec
definition, (2) universal HOL equation by induction matching the
symbol's defining recursion, (3) `PROV_PRST_PR_EVAL` to lift.

#### §3a. Missing PRST infrastructure blocking §3

The substitute / numeral / diag clauses in §3 are not blocked by the DSL
itself (see `doc/dsl_spec.md`); they are blocked by missing PRST-domain
primitives. These have now been landed as `p.sorry()` stubs in
`prst_proof.py` (between `PROV_PRST_ADJ_DEF_AT` and the mu-correctness
axiom block) so that consumers can import them and proofs can be
written assuming the signatures. The schemas at the parent level
(`PROV_PRST_REC_BASE_DEF`, etc.) are *not* sorried — only their applied
forms.

Sole stub (Paulson-form unifier):

- `PROV_PRST_PR_DEF_AT_LIFT` —
  `is_pr_sym F /\ App_pt F args = body
   ==> Prov_PRST (Eq_pf (App_pt F args) body)`.
  Single-step PR-def AT-lifting schema. Per-symbol AT specialisations
  (proj 1 / proj 3_0/1/2 / proj 4_2 / rec_base/step /
  course_rec_base/step / if_in_true/false / const /
  pair_left/right/ord / comp 1/2/3) are not stubbed as named
  theorems. Downstream consumers SPEC the schema at the specific PR
  symbol, discharge the HOL antecedent `App_pt F args = body` by
  `REFL` or the symbol's defining HOL equation, and use the
  resulting `Prov_PRST (Eq_pf (App_pt F args) body)`. If a downstream
  caller invokes a specific specialisation often enough that a named
  lemma earns its keep, introduce it then as a real (non-sorry)
  theorem.

PRST equality congruence layer.

Sole stub (Paulson-form unifier):

- `PROV_PRST_EQ_LEIBNIZ` —
  `Prov_PRST (Eq_pf a b) /\ Prov_PRST (substitute_p F v a)
   ==> Prov_PRST (substitute_p F v b)`.
  The substitution-of-equals (function-context equality) schema.
  Derives from the propositional logical axioms +
  `PROV_PRST_REFL` + `PROV_PRST_SUBST` in the standard
  Świerczkowski / Paulson HF derivation.

`PROV_PRST_EQ_SYM`, `_EQ_TRANS`, `_EQ_CONG_APP_PT_ARG`,
`_EQ_CONG_TUP_PT`, and `_EQ_CONG_PAIR_ORD` are not stubbed as named
theorems. They are 3-5 line Leibniz instantiations of
`PROV_PRST_EQ_LEIBNIZ` (see its docstring for the explicit
context/seed for each) and are inlined at the call site. If a
downstream caller invokes the same pattern often enough that a
named lemma earns its keep, introduce it then as a real (non-sorry)
theorem.

Singleton-membership Prov_PRST facts
(`PROV_PRST_IN_PA_SINGLETON_SELF`, `PROV_PRST_NOT_IN_PA_SINGLETON`)
were previously stubbed as antecedents for the deleted
`PROV_PRST_IF_IN_TRUE/FALSE_DEF_AT` stubs. With no remaining
consumers they have been removed; downstream uses of PR-level
singleton membership derive directly through `PROV_PRST_PR_EVAL` or
`PROV_PRST_PR_DEF_AT_LIFT` at the call site.

### 4. Representation Bridges

These are downstream of the evaluator and checker API. Keep this layer to the
concrete bridge obligations used downstream.

- `SUBSTITUTE_REPRESENTS_PRST`
- `DIAG_REPRESENTS_PRST`
- `PROV_PRST_REPRESENTS`

### 5. G1 Stack

These are the first-incompleteness targets after the checker, evaluator, and
representation bridges are in place.

- `DIAGONAL_LEMMA_PRST`
- `G_PRST_DIAGONAL_EQ`
- `PRST_CONSISTENT`
- `PRST_SIGMA1_SOUND`
- `GODEL_FIRST_PRST`
- `PRST_ESSENTIALLY_UNDECIDABLE`

### 6. G2 Stack

These remain after G1. `MP_COMBINE_PR_CORRECT` is listed earlier because its
proof depends on the checker/list-combine API, not on Loeb.

- `IS_PFORM_CON_PRST`
- `DERIV_D1`
- `DERIV_D2`
- `DERIV_D3`
- `LOEB_PRST`
- `GODEL_SECOND_PRST`
- `PRST_CANNOT_PROVE_OWN_CONSISTENCY`

## PR Symbol Evaluator Spikes

These are short validation tasks for the main unknowns on the PRST
evaluator path. They are not additional `p.sorry()` sites; they are meant to
decide whether the remaining proof debt stays local or expands into larger
representability work.

### Design 1 — Boolean Helper Correctness

Purpose: prove the small PR boolean helper facts once, then reuse them
everywhere.

Design facts:

- `eq_nat_pr` returns `T_pt` exactly on equal nat0 inputs.
- `or_bool_pr` and `and_bool_pr` agree with the `T_pt`/`F_pt` convention.
- `T_PT_NEQ_F_PT` is available before evaluator correctness proofs consume it.

Settled shape:

- `T_pt` and `F_pt` are distinct.
- `eq_nat_pr x y` returns `T_pt` exactly when `x = y`, and `F_pt` otherwise.
- `or_bool_pr` and `and_bool_pr` are ordinary boolean connectives under the
  boolean-input invariant `x,y in {T_pt,F_pt}`.
- Outside that invariant, the helpers intentionally branch on exactly
  `x = T_pt`: `or_bool_pr x y` returns `y` when `x != T_pt`, and
  `and_bool_pr x y` returns `F_pt` when `x != T_pt`.
- Under boolean inputs, the reusable algebra includes identity, annihilator,
  associativity, and distributivity facts needed by `is_pr_refl_pr`,
  `mem_t_pr`, and proof-list checker correctness.

The executable reference design is `prst_bool_spike.py`.

Production proof obligations: prove these helper evaluation lemmas once from
the `if_in_sym` defining equations and `T_PT_NEQ_F_PT`, then require downstream
checker proofs to establish the boolean-input invariant before using boolean
algebra rewrites.

### Design 2 — `is_pterm_pr` Correctness Slice

Purpose: pin the PR-level term recognizer used by reflexivity and proof-checker
examples.

Design facts:

- `is_pterm_pr Empty_pt = T_pt`.
- `is_pterm_pr (Tup_pt a b) = T_pt` from recursive `a`/`b` truth.
- `is_pterm_pr (App_pt f args) = T_pt` from `is_partial_pr_sym f` and args.
- `is_pr_refl_pr (Eq_pf t t) = T_pt` when the Eq shape is reflexive and
  `is_pterm_pr t = T_pt`.

Settled shape:

- `is_pterm_pr` is modeled as a Pair_ord course recursion returning
  `Pair_ord(is_term_bool, child_bool_pair)`, not as a direct syntax recursion.
- `Empty_pt`, `Var_pt`, `Tup_pt`, and `App_pt` have the expected boolean
  behavior. The `Tup_pt` branch consumes the two child booleans carried by the
  intermediate payload pair.
- The `App_pt` branch checks the function id with the syntactic
  `is_partial_pr_sym_pr` predicate and checks only the argument tuple through
  the payload's right child boolean.
- Representative reflexivity formulas such as `Eq_pf t t` with nontrivial
  `App_pt`/`Tup_pt` terms are accepted by `is_pr_refl_pr`; malformed non-term
  payloads and invalid App heads are rejected.

The executable reference design is `prst_pterm_spike.py`.

Production proof obligations: prove the corresponding PR evaluation lemmas for
the auxiliary course recursion, then use them to derive
`is_pr_refl_pr (Eq_pf t t) = T_pt` from the HOL-side `is_pterm t` theorem for
the representative constructor cases.

### Design 3 — `is_pr_axiom_pr` Leaf Alignment

Purpose: keep the PR checker leaf aligned with the HOL recognizer
branch-by-branch.

Branch contract:

- Direct and substituted PR-def axioms are accepted through
  `is_pr_def_instance_pr`.
- PRST reflexivity formulas such as
  `Eq_pf (App_pt adj_sym args) (App_pt adj_sym args)` are accepted through
  `is_pr_refl_pr`, guarded by `is_pterm_pr`.
- Propositional Hilbert schemas are accepted through `is_logical_axiom_pr`.

The PR-side recognizer has real bodies for the three leaves:

- `is_pr_def_instance_pr` is a disjunction of PR-level schema matchers.
  Each matcher reads schema parameters from the candidate formula, reconstructs
  the relevant PR-def template, and checks that the candidate is either the
  direct template or a one-variable `substitute_p` instance of that template.
- `is_pterm_pr` uses a Pair_ord course recursion for `Empty_pt`, `Var_pt`,
  `Tup_pt`, and `App_pt`, with App heads checked by a syntactic
  `is_partial_pr_sym_pr` shape recognizer.
- `is_logical_axiom_pr` recognizes the propositional K/S/N Hilbert schemas by
  PR-level destructuring of `Imp_pf`/`Not_pf` shapes.

`is_pr_def_instance_pr` must not search arbitrary `F,t,v < n`. Substitution can
shrink fixed `Var_pt` leaves, so a numeric bound on the pre-substitution axiom
is not a stable invariant. The settled design is schema-specific matching:

- For closed templates with no free `Var_pt` slots, accept the direct template.
- For fixed-arity schemas, destructure the candidate formula and verify each
  repeated formal slot against the extracted replacement term.
- For variable-arity schemas such as `proj_def_axiom_at i n`, read the schema
  parameters from the candidate symbol payload, check the HOL-side guard
  (`i < n`), walk the argument tuple, and verify one consistent substituted
  formal slot.
- For parametric schemas such as `rec`, `const`, `course_rec`, and `pair_*`,
  read the parameters from the candidate shape and use the same one-variable
  substitution-instance check, including nested parameter occurrences such as
  the RHS of `const_def_axiom_at c`.

The executable reference design is `prst_def_instance_spike.py`. It covers every
current `is_pr_def` axiom family: `zero`, `proj`, `if_in_true`,
`if_in_false`, `rec_base`, `rec_step`, `const`, `course_rec_base`,
`course_rec_step`, `pair_left`, `pair_right`, and `pair_ord`, including
malformed near-misses.

Production requirements: mechanise the reference design at PR level with tuple
walkers, PR-level guards such as `nat0_lt`/`is_pr_sym`, and reusable
substitution-instance checker components for schema parameters.

### Design 4 — `substitute_pr` External Correctness Slice

Purpose: pin the external correctness proof shape for `substitute_pr`.

Design facts:

- `substitute_pr Empty_pt t v` evaluates to `Empty_pt`.
- `substitute_pr (Eq_pf a b) t v` evaluates to
  `Eq_pf (substitute_p a t v) (substitute_p b t v)`.
- `App_pt`/`Tup_pt` nested examples evaluate by the same constructor-recursive
  equation as HOL-side `substitute_p`.

Settled shape:

- The Pair_ord course-recursive `substitute_pr` model agrees with direct
  `substitute_p` syntax recursion on `Empty_pt`, `Var_pt`, `Tup_pt`, `Eq_pf`,
  `In_pa`, `Not_pf`, `Imp_pf`, and nested examples.
- The `App_pt` branch is non-uniform in the intended way: it preserves the
  function id exactly and recurses only into the argument tuple.
- The raw default Pair_ord branch is enough to make constructor payload pairs
  carry the recursively substituted child values, which is what the `Eq_pf`,
  `Tup_pt`, and `App_pt` cases consume.
- If the target variable is absent from a well-formed example, the result is
  unchanged.

The executable reference design is `prst_substitute_spike.py`.

Production proof obligations: prove the external correctness theorem by a
single course-recursion induction over the encoded formula/term, with
constructor-specific rewrite lemmas for the Var hit/miss case, the default
payload-pair case, and the App non-uniform function-id case.

### Design 5 — `Proof_PRST_pr` List Checker Slice

Purpose: pin the proof-list checker recursion before proving full correctness.

Design facts:

- Singleton axiom list: `Proof_PRST_pr (Tup_pt a Empty_pt, a) = T_pt` when
  `is_pr_axiom_pr a = T_pt`.
- Two-line MP list: from lines `f` and `Imp_pf f g`, appending `g` validates.
- Negative empty-list case: `Proof_PRST_pr (Empty_pt, n) = F_pt`.

Settled shape:

- Proof lists use the same final-line-first `Tup_pt` orientation as
  `Proof_PRST`.
- singleton axiom proof lists validate from the `is_pr_axiom_pr` leaf;
- `Empty_pt` never validates as a proof list;
- a new head `g` validates by MP when the tail already contains both `f` and
  `Imp_pf f g`.
- negative cases cover non-`Tup_pt` proof inputs, malformed list tails, invalid
  axiom singletons, wrong targets, MP missing the antecedent, MP missing the
  implication, and nearby nonmatching implications;
- ordering and duplicate-line cases validate because MP uses membership in the
  full earlier-list tail.

The executable reference design is `prst_checker_spike.py`.

The current `Proof_PRST_pr` body in `prst_pr.py` matches this decomposition:
top-level `is_tup_pr`, head equality via `tup_head_pr`, full-list validation
via `valid_proof_list_pr`, membership via `mem_t_pr`, and MP search via
`exists_mp_witness_pr`.

Production proof obligations (PR-native; no HOL twin chain): callers needing
a structured view of `App_pt Proof_PRST_pr ... = T_pt` reduce through the
existing `PROOF_PRST_PR_BOOL_VIEW` (which expresses the body as an
`and_bool_pr` chain of `is_tup_pr`, head-eq, and `valid_proof_list_pr`
checks) and reason about the underlying PR predicates directly.

One separate G2-only blocker remains for the D2/proof-combinator path:
`mp_combine_pr` in `prst_godel2.py` is still the constant-0 stub, so the
two-line checker shape is validated only for an explicit proof list, not yet
for `App_pt mp_combine_pr ...`.

### Design 6 — Internal Evaluation Chain

Purpose: ensure that external PR-symbol correctness can be lifted into PRST
provability without recreating HF-style representability packages.

Reference coverage:

- `PROV_PRST_NUMERAL_EVAL` by induction on arbitrary `n`.
- `PROV_PRST_SUBSTITUTE_EVAL` by constructor recursion over all PRST syntax
  families.
- `PROV_PRST_DIAG_EVAL` by composition of `diag_pr`, numeral evaluation, and
  substitute evaluation.

Design criterion: each evaluation theorem follows from PR-def instances plus
`PROV_PRST_AX`, `PROV_PRST_SUBST`, `PROV_PRST_MP`, and equality reasoning,
not from a new global representability axiom.

Settled shape:

- `PROV_PRST_NUMERAL_EVAL` is modeled by induction on `n`: base uses the
  recursor base equation plus `zero_def_axiom`; successor uses the recursor
  step equation, the predecessor evaluation, and the `adj`/`Adj_pt` equation.
- `PROV_PRST_SUBSTITUTE_EVAL` is modeled by constructor recursion over every
  PRST syntax family: `Empty_pt`, `Var_pt` hit/miss, `Tup_pt`, `App_pt`,
  `Eq_pf`, `In_pa`, `Not_pf`, `Imp_pf`, and opaque atom/default cases.
- The `App_pt` substitution case records the non-uniform obligation that the
  function id is preserved exactly while only the argument tuple recurses.
- `PROV_PRST_DIAG_EVAL` is modeled as composition of the `diag_pr` definition,
  numeral evaluation, substitute evaluation, and equality reasoning.
- The proof-plan checker rejects any use of a global representability axiom;
  all leaves are PR-def instances, `PROV_PRST_AX`, `PROV_PRST_SUBST`,
  `PROV_PRST_MP`, or PRST equality reasoning.

The executable reference design is `prst_internal_eval_spike.py`.

Production proof obligations: expose the local PRST equality API needed for
reflexivity, symmetry, transitivity, and congruence; mechanise the generic
`PRST_INTERNALIZES_TRUE_PR_EVAL` boundary for true PR computations; then
mechanise the numeral induction, substitute constructor recursion, and diag
composition recorded by the reference. No global representability axiom is
part of the G1 internal-evaluation bridge.

### Spike 7 — `mu` Strength Check

Goal: verify that the current sole explicit axiom, `MU_CORRECTNESS`, is enough
for the planned proof-search witness.

Target fact:

- If `Proof_PRST_pr p n = T_pt`, then the `find_proof_pr`/`mu_sym` witness
  application also checks as a proof of `n`.

Success criterion: no leastness or totality property of `mu` is needed for G1;
only the current correctness direction is consumed.

Status: passed. `FIND_PROOF_PR_MU_CORRECT` proves the target specialization
from `MU_CORRECTNESS` alone:

```text
|- !pf n.
     App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = T_pt
     ==> App_pt Proof_PRST_pr
           (Tup_pt (App_pt find_proof_pr (Tup_pt n Empty_pt))
                   (Tup_pt n Empty_pt)) = T_pt
```

The proof only uses `is_pr_sym Proof_PRST_pr`, the generic lift to
`is_partial_pr_sym`, `MU_CORRECTNESS`, and the definition
`find_proof_pr = mu_sym Proof_PRST_pr`.
