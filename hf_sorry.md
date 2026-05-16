# HF Gödel-I remaining `sorry()` plan

This file tracks substantive HF/G1 proof debt. Historical phase notes,
closed items, and hygiene-only internal-expression checks are omitted.

Current inventory command:

```sh
rg -n "p\.sorry\(" hf_*.py
```

At the time of this update, the HF path has no direct `new_axiom` calls:

```sh
rg -n "new_axiom" hf_*.py
```

All remaining proof debt is visible as named `@proof` stubs using
`p.sorry()`. This document intentionally filters out hygiene-only stubs
whose role is just internal body well-formedness/free-variable bookkeeping.

## Live Inventory

| Group | File | Count | Role |
|---|---|---:|---|
| A | `hf_repr_core.py`, `hf_repr_subst.py` | 4 | support predicate and substitution packages |
| B | `hf_repr_thms.py` | 8 | internal proof-checker representability |
| C | `hf_godel1.py` | 6 | diagonal-function and diagonal-lemma layer |

Total tracked substantive HF/G1 stubs: **20**.

The Group B count rose by two relative to the older inventory: the
former `PROV_HF_REPRESENTS_BWD` stub was retired in favor of the
Sigma_1-soundness instantiation `SIGMA1_SOUNDNESS_PROV_HF_INTERNAL`,
and two new Hilbert-Bernays-Loeb derivability-condition stubs
(`PROV_HF_INTERNAL_D2`, `PROV_HF_INTERNAL_D3`) were added because the
target now covers both halves of G1 plus G2.

## Dependency Order

Clear the remaining sorries in this order:

1. `hf_repr_subst.py` substitution representability package.
2. `hf_repr_subst.py` substitution equivalence package.
3. `hf_repr_core.py` support predicate and support equivalence packages.
4. `hf_repr_thms.py` recognizer representability.
5. `hf_repr_thms.py` valid-step and proof-set representability.
6. `hf_repr_thms.py` `PROV_HF_REPRESENTS_FWD` (= derivability condition D1).
7. `hf_repr_thms.py` `PROV_HF_INTERNAL_D2` and `PROV_HF_INTERNAL_D3`
   (Hilbert-Bernays-Loeb conditions for G2).
8. `hf_repr_thms.py` `SIGMA1_SOUNDNESS_PROV_HF_INTERNAL` (irrefutability
   lever for G1, replaces BWD).
9. `hf_godel1.py` diagonal function package.
10. `hf_godel1.py` HOL substitution/free-variable lemmas.
11. `hf_godel1.py` final diagonal lemma.

The most useful immediate target is group A. Group B depends on the
support equivalences and substitution package. Group C depends on the
representability path plus ordinary substitution/free-variable facts.

## Group A — `hf_repr_core.py`, `hf_repr_subst.py`

### A1. Substitution Packages

Live stubs:

```text
HF_SUBSTITUTE_REPRESENTS_PACKAGE
HF_SUBSTITUTE_EQUIV_PACKAGE
```

Exported from `hf_repr_subst.py`:

```text
SUBSTITUTE_REPRESENTS_SYNTACTIC
SUBSTITUTE_REPRESENTS_TERM
SUBSTITUTE_REPRESENTS_FORM
SUBSTITUTE_INTERNAL_EQUIV
SUBSTITUTE_INTERNAL_FUNCTIONAL
```

Purpose:

These packages localize all substitution graph semantics in
`hf_repr_subst.py`.

`HF_SUBSTITUTE_REPRESENTS_PACKAGE` proves the forward/existence theorem:

```text
!F t v. (is_term F \/ is_form F) ==>
  Prov_HF substitute_internal(F,t,v,substitute F t v)
```

`HF_SUBSTITUTE_EQUIV_PACKAGE` proves the syntactic-input equivalence:

```text
!F t v r. (is_term F \/ is_form F) ==>
  (Prov_HF substitute_internal(F,t,v,r) = (r = substitute F t v))
```

Expected path:

* Prove by strong induction over the encoded HF syntax grammar.
* Keep graph-witness construction and uniqueness private to these
  packages, not exposed as raw graph reconstruction theorems.
* The representability package should come first; the equivalence package
  can then reuse existence plus the local graph-determinism argument.

`HF_SYNTAX_REC_PACKAGE` is now only a compatibility alias for
`HF_SUBSTITUTE_REPRESENTS_PACKAGE`.

### A2. Support Predicate Package

Live stub:

```text
HF_SUPPORT_PREDICATE_PACKAGE
```

Purpose:

Positive and negative representability of:

```text
is_term_internal
is_form_internal
free_in_internal
```

Expected path:

* Use syntax induction over terms/forms.
* Positive cases follow constructors.
* Negative cases use constructor disjointness and recognizer recurrences.
* `free_in_internal` follows the recursive `FREE_IN_AT_*` facts.

This package should be proved before the equivalence package.

### A3. Support Equivalence Package

Live stub:

```text
HF_SUPPORT_EQUIV_PACKAGE
```

Purpose:

Exports equivalences:

```text
is_term n = Prov_HF (is_term_internal[quote_hf n])
is_form n = Prov_HF (is_form_internal[quote_hf n])
free_in F v = Prov_HF (free_in_internal[quote_hf F, quote_hf v])
```

Expected path:

* Forward recognizer/free-variable directions come from A2.
* Reverse directions come from the negative clauses in A2.

Note:

This theorem is a package for downstream convenience. If it becomes too
large, split it into three named theorem stubs and repackage only after
the pieces are proved.

## Group B — `hf_repr_thms.py`

### B1. Recognizer Representability

Live stubs:

```text
IS_AXIOM_INTERNAL_REPRESENTS
```

Purpose:

Prove that true external recognizer predicates are internally provable
after filling with quoted inputs.

Expected path:

* Split `is_axiom` into HF, HF-induction, and logical cases.
* Use support equivalences from group A.
* Repack through `is_axiom_internal`.

### B2. Valid-Step Representability

Live stubs:

```text
VALID_STEP_HF_SET_INTERNAL_MP_CASE
VALID_STEP_HF_SET_INTERNAL_GEN_CASE
VALID_STEP_HF_SET_INTERNAL_REPRESENTS
```

Purpose:

Prove that each externally valid proof step is represented by the
internal `valid_step_hf_set_internal` formula.

Expected path:

* Axiom case uses `IS_AXIOM_INTERNAL_REPRESENTS`.
* MP/Gen cases use:
  * `QUOTE_HF_MEM_DECISION` for membership premises;
  * quoted `Pair_ord` record-shape bridge;
  * the corresponding recognizer body facts;
  * witnesses for the existential branch.
* General theorem splits `VALID_STEP_HF_SET_AT` and dispatches to the
  three case theorems.

Main missing reusable lemma:

```text
quote_hf (Pair_ord i f)
= qparse Pair_ord shape over quote_hf i and quote_hf f
```

The earlier `QUOTE_HF_AT_PAIR_ORD` requires an ordering side condition.
The valid-step proof wants a record-shape bridge robust enough for proof
records, ideally derived from quoted finite-set extensionality instead
of from `nat0_lt i f`.

Recommended order:

1. Prove the quoted record-shape bridge.
2. `VALID_STEP_HF_SET_INTERNAL_GEN_CASE`
3. `VALID_STEP_HF_SET_INTERNAL_MP_CASE`
4. `VALID_STEP_HF_SET_INTERNAL_REPRESENTS`

### B3. Proof-Set Representability

Live stub:

```text
PROOF_HF_SET_INTERNAL_REPRESENTS
```

Purpose:

Lift valid-step representability from one step to a whole finite HF
proof set.

Expected path:

* Rewrite `Proof_HF_set P n` with `PROOF_HF_SET_AT`.
* Use the root proof-record membership to prove the internal root
  conjunct.
* For the internal universal condition, decode each quoted proof record
  from a membership premise in `quote_hf P`.
* Apply `VALID_STEP_HF_SET_INTERNAL_REPRESENTS` to each decoded record.
* Introduce the quoted root dependency-set witness.

Main missing reusable lemma:

```text
membership in quote_hf P as a proof-record term
=> corresponding external record is in P
```

This is the finite quoted-set elimination lemma. It is the second
important bridge after the quoted `Pair_ord` record-shape bridge.

### B4. Provability Representability and Derivability Conditions

Live stubs:

```text
PROV_HF_REPRESENTS_FWD                  (D1)
PROV_HF_INTERNAL_D2                     (D2)
PROV_HF_INTERNAL_D3                     (D3)
SIGMA1_SOUNDNESS_PROV_HF_INTERNAL       (Sigma_1-soundness)
PROV_HF_REPRESENTS
```

Target coverage:

* G1 unprovability half (Con ==> ~Prov_HF G):
  needs `PROV_HF_REPRESENTS_FWD` only.
* G1 irrefutability half (Con ==> ~Prov_HF (Not_f G)):
  needs `SIGMA1_SOUNDNESS_PROV_HF_INTERNAL` (which replaces the old
  BWD stub).
* G2 (Con ==> ~Prov_HF Con_HF):
  needs the full Hilbert-Bernays-Loeb chain
  D1 = `PROV_HF_REPRESENTS_FWD`,
  D2 = `PROV_HF_INTERNAL_D2`,
  D3 = `PROV_HF_INTERNAL_D3`.
  D3 is the load-bearing piece: it internalizes the proof of D1.

D1 -- forward direction:

```text
Prov_HF n
==> Prov_HF (substitute Prov_HF_internal (quote_hf n) idx_x)
```

Expected path:

* Rewrite `Prov_HF n` with `PROV_HF_AT`.
* Choose proof-set witness `P`.
* Apply `PROOF_HF_SET_INTERNAL_REPRESENTS`.
* Unfold `Prov_HF_internal` and introduce witness `quote_hf P`.
* Rewrite template filling to public substitution form.

D2 -- internal modus ponens for `Prov_HF_internal`:

```text
is_form F /\ is_form G ==>
Prov_HF (Imp_f (substitute Prov_HF_internal (quote_hf (Imp_f F G)) idx_x)
               (Imp_f (substitute Prov_HF_internal (quote_hf F) idx_x)
                      (substitute Prov_HF_internal (quote_hf G) idx_x)))
```

Expected path:

* Internalize the external MP rule on proof records.
* Combine `IS_MP_INTERNAL_REPRESENTS` with internal existential
  introduction lifted across the implication.

D3 -- provable Sigma_1-completeness for `Prov_HF_internal`:

```text
is_form F ==>
Prov_HF (Imp_f (substitute Prov_HF_internal (quote_hf F) idx_x)
               (substitute Prov_HF_internal
                           (quote_hf (substitute Prov_HF_internal
                                                 (quote_hf F) idx_x))
                           idx_x))
```

Expected path:

* Formalize the proof of `PROV_HF_REPRESENTS_FWD` inside HF.
* This is the analogue of the metatheoretic Sigma_1-completeness for
  the specific predicate `Prov_HF_internal`.
* This stub is the largest single piece on the road to G2 and should
  only be undertaken once D1, D2 and the support packages are stable.

Sigma_1-soundness instantiation (replacement for BWD):

```text
Prov_HF (substitute Prov_HF_internal (quote_hf n) idx_x)
==> Prov_HF n
```

Status:

* Treated as a derived rule justified by Sigma_1-soundness of HF
  applied to the specific Sigma_1 formula `Prov_HF_internal[quote_hf n]`.
* This replaces the earlier `PROV_HF_REPRESENTS_BWD` stub, which
  framed the same statement as a model-theoretic / proof-extraction
  obligation. The new framing makes the dependency on Sigma_1-soundness
  explicit and avoids committing to a Stage-6 semantic interpretation
  layer.

Final wrapper:

`PROV_HF_REPRESENTS` is immediate from D1 plus
`SIGMA1_SOUNDNESS_PROV_HF_INTERNAL`.

## Group C — `hf_godel1.py`

### C1. Diagonal Function Package

Live stubs:

```text
DIAG_REPRESENTS
DIAG_FUNCTIONAL
```

Purpose:

Represent the meta function:

```text
diag n = substitute n (quote_hf n) var_x
```

Expected path:

* Define or expose `diag_internal` as a composition around
  `substitute_internal`.
* `DIAG_REPRESENTS` should use `SUBSTITUTE_REPRESENTS_FORM`.
* `DIAG_FUNCTIONAL` should use `SUBSTITUTE_INTERNAL_FUNCTIONAL`.

This group depends on the group-A substitution graph package.

### C2. HOL Substitution/Free-Variable Lemmas

Live stubs:

```text
VAR_X_NEQ_SUC0_0
SUBSTITUTE_FREE_NO_OP
FREE_IN_SUBSTITUTE_AT_DIFFERENT_VAR
```

Expected path:

* `VAR_X_NEQ_SUC0_0`:
  direct constructor/tag disjointness for `Var_t 0` versus `SUC0 0`.
* `SUBSTITUTE_FREE_NO_OP`:
  structural induction over terms/forms using `SUBSTITUTE_AT_*` and
  `FREE_IN_AT_*`.
* `FREE_IN_SUBSTITUTE_AT_DIFFERENT_VAR`:
  structural induction over terms/forms; binder case is the only one
  likely to need care.

These are HOL-level syntax facts, not object-level `Prov_HF`
representability facts. They should be cleared before the final
diagonal lemma.

### C3. Diagonal Lemma

Live stub:

```text
DIAGONAL_LEMMA
```

Purpose:

For any one-free-variable formula `phi`, build:

```text
psi = diag (theta_of_phi phi)
```

and prove:

```text
is_form psi
/\ Prov_HF (Iff_f psi (substitute phi (quote_hf psi) var_x))
```

Expected path:

* Use formula-constructor closure to prove the `is_form` conjunct.
* Compute substitutions through `theta_of_phi`.
* Use `DIAG_REPRESENTS` at `theta_of_phi phi`.
* Use `DIAG_FUNCTIONAL` to identify the existential witness with
  `quote_hf psi`.
* Use existing HF propositional machinery:
  * `PROV_HF_AND_INTRO`
  * `PROV_HF_AND_ELIM_LEFT`
  * `PROV_HF_AND_ELIM_RIGHT`
  * `PROV_HF_EXISTS_INTRO`
  * `PROV_HF_EXISTS_ELIM`
  * `PROV_HF_IFF_INTRO`

This is the final assembly theorem for the G1 diagonal sentence. Do it
after C1 and C2.

## Practical Next Step

Start with `HF_SUBSTITUTE_REPRESENTS_PACKAGE`.

Reasons:

* It is the constructive half needed by downstream representability.
* It can keep graph-witness construction private instead of exposing raw
  graph reconstruction theorem names.
* `HF_SUBSTITUTE_EQUIV_PACKAGE` can then focus on uniqueness/determinism
  for syntactic inputs.
