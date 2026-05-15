# HF Gödel-I remaining `sorry()` plan

This file tracks only live HF/G1 proof debt. Historical phase notes and
closed items are omitted.

Current inventory command:

```sh
rg -n "p\.sorry\(" hf_*.py
```

At the time of this update, the HF path has no direct `new_axiom` calls:

```sh
rg -n "new_axiom" hf_*.py
```

All remaining proof debt is therefore visible as named `@proof` stubs
using `p.sorry()`.

## Live Inventory

| Group | File | Count | Role |
|---|---|---:|---|
| A | `hf_repr_core.py` | 15 | support predicate and substitution packages |
| B | `hf_repr_thms.py` | 11 | internal proof-checker representability |
| C | `hf_godel1.py` | 8 | diagonal-function and diagonal-lemma layer |

Total live HF/G1 stubs: **34**.

## Dependency Order

Clear the remaining sorries in this order:

1. `hf_repr_core.py` substitution constructor rules.
2. `hf_repr_core.py` syntax-recursion package.
3. `hf_repr_core.py` support predicate and support equivalence packages.
4. `hf_repr_core.py` qparse/body side-condition packages.
5. `hf_repr_thms.py` recognizer representability.
6. `hf_repr_thms.py` valid-step and proof-set representability.
7. `hf_repr_thms.py` `PROV_HF_REPRESENTS_FWD`.
8. Defer or isolate `PROV_HF_REPRESENTS_BWD` as Stage-6 soundness.
9. `hf_godel1.py` diagonal function package.
10. `hf_godel1.py` HOL substitution/free-variable lemmas.
11. `hf_godel1.py` final diagonal lemma.

The most useful immediate target is group A. Group B depends on the
support equivalences and substitution package. Group C depends on the
representability path plus ordinary substitution/free-variable facts.

## Group A — `hf_repr_core.py`

### A1. Substitute Constructor Rules

Live stubs:

```text
SUBSTITUTE_REC_EMPTY
SUBSTITUTE_REC_VAR_HIT
SUBSTITUTE_REC_VAR_MISS
SUBSTITUTE_REC_INSERT
SUBSTITUTE_REC_EQ
SUBSTITUTE_REC_IN
SUBSTITUTE_REC_NOT
SUBSTITUTE_REC_IMP
SUBSTITUTE_REC_FORALL_HIT
SUBSTITUTE_REC_FORALL_MISS
```

Purpose:

These are the constructor-local object proofs for
`substitute_internal`. They say the internal graph relation proves the
same result as the HOL recursive function `substitute` on each syntax
constructor.

Expected path:

* Unfold the filled `substitute_internal` body.
* Use the corresponding `SUBSTITUTE_AT_*` theorem from `hf_syntax.py`.
* Use recursive graph hypotheses in binary/unary constructor cases.
* Rebuild the output constructor with existing HF propositional and
  equality rules.

Recommended order:

1. `SUBSTITUTE_REC_EMPTY`
2. `SUBSTITUTE_REC_VAR_HIT`
3. `SUBSTITUTE_REC_VAR_MISS`
4. `SUBSTITUTE_REC_NOT`
5. `SUBSTITUTE_REC_INSERT`
6. `SUBSTITUTE_REC_EQ`
7. `SUBSTITUTE_REC_IN`
8. `SUBSTITUTE_REC_IMP`
9. `SUBSTITUTE_REC_FORALL_HIT`
10. `SUBSTITUTE_REC_FORALL_MISS`

Why this order:

The first three establish the shape of direct internal-graph proofs.
`Not_f` is the smallest recursive constructor case. `Insert_t`,
`Eq_f`, `In_a`, and `Imp_f` share the binary-constructor pattern.
The binder cases come last because they combine constructor work with
side conditions.

### A2. Syntax Recursion Package

Live stub:

```text
HF_SYNTAX_REC_PACKAGE
```

Purpose:

This is the scoped recursion/induction eliminator used to derive
`SUBSTITUTE_REPRESENTS_SYNTACTIC` from the ten constructor rules.

Expected path:

* Prove by strong induction over the encoded HF syntax grammar.
* Split on `is_term F \/ is_form F`.
* Use `IS_TERM_REC` and `IS_FORM_REC` to expose constructors.
* Apply the corresponding constructor rule.
* Use induction hypotheses for strict subterms/subformulas.

This is the main local theorem in group A. It should become much easier
after A1 is proved because the package can be attacked structurally
instead of carrying object-formula details.

### A3. Support Predicate Package

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

### A4. Support Equivalence Package

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
substitute_internal(...) = graph(substitute)
```

Expected path:

* Forward recognizer/free-variable directions come from A3.
* Reverse directions come from the negative clauses in A3.
* Substitute graph equivalence uses:
  * `SUBSTITUTE_REPRESENTS_SYNTACTIC`
  * `SUBSTITUTE_INTERNAL_FUNCTIONAL`

Note:

This theorem is a package for downstream convenience. If it becomes too
large, split it into four named theorem stubs and repackage only after
the pieces are proved.

### A5. Qparse and Body Side Conditions

Live stubs:

```text
HF_PACKAGE_SIDE_CONDITION_PACKAGE
HF_PROV_FREE_CONDITION_PACKAGE
```

Purpose:

These prove `is_form` and `free_in` facts for qparse-built internal
bodies, especially:

```text
is_axiom_internal
Prov_HF_internal
Pair_ord / Imp_f / Forall_f qparse terms
```

Expected path:

* Expand the qparse-built `Insert_t` towers.
* Use `IS_TERM_EMPTY`, `IS_TERM_INSERT`, and constructor form rules.
* Use `FREE_IN_AT_INSERT` plus closedness of qparse tags.
* For `Prov_HF_internal`, unfold its existential over
  `Proof_HF_set_internal`; the bound proof-set slot disappears, leaving
  only `idx_x`.

These should be cleared before the high-level `hf_repr_thms.py`
representability proofs.

## Group B — `hf_repr_thms.py`

### B1. Recognizer Representability

Live stubs:

```text
IS_AXIOM_INTERNAL_REPRESENTS
IS_MP_INTERNAL_REPRESENTS
IS_GEN_INTERNAL_REPRESENTS
```

Purpose:

Prove that true external recognizer predicates are internally provable
after filling with quoted inputs.

Expected path:

* `IS_MP_INTERNAL_REPRESENTS`:
  * rewrite with `IS_MP_AT`;
  * reduce filled internal body to quoted object equality;
  * close with `PROV_HF_REFL`.
* `IS_GEN_INTERNAL_REPRESENTS`:
  * rewrite with `IS_GEN_AT`;
  * introduce the quoted binder witness;
  * close the resulting quoted equality.
* `IS_AXIOM_INTERNAL_REPRESENTS`:
  * split `is_axiom` into HF, HF-induction, and logical cases;
  * use support equivalences from group A;
  * repack through `is_axiom_internal`.

Recommended order:

1. `IS_MP_INTERNAL_REPRESENTS`
2. `IS_GEN_INTERNAL_REPRESENTS`
3. `IS_AXIOM_INTERNAL_REPRESENTS`

MP and Gen are smaller and will exercise the template-fill/qparse
mechanics before the axiom schemas.

### B2. Valid-Step Representability

Live stubs:

```text
VALID_STEP_HF_SET_INTERNAL_AXIOM_CASE
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
  * `IS_MP_INTERNAL_REPRESENTS` or `IS_GEN_INTERNAL_REPRESENTS`;
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
2. `VALID_STEP_HF_SET_INTERNAL_AXIOM_CASE`
3. `VALID_STEP_HF_SET_INTERNAL_GEN_CASE`
4. `VALID_STEP_HF_SET_INTERNAL_MP_CASE`
5. `VALID_STEP_HF_SET_INTERNAL_REPRESENTS`

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

### B4. Provability Representability

Live stubs:

```text
PROV_HF_REPRESENTS_FWD
PROV_HF_REPRESENTS_BWD
PROV_HF_REPRESENTS
```

Forward direction:

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

Backward direction:

```text
Prov_HF (substitute Prov_HF_internal (quote_hf n) idx_x)
==> Prov_HF n
```

Status:

This is not part of the finite proof-checker representability
construction. It is the soundness/reflection direction: from an HF proof
of the internal Sigma-style predicate, extract a real finite proof set.

Recommended handling:

* Do not let this block G1 forward representability.
* Keep it isolated as Stage-6 soundness unless the target theorem
  strictly requires biconditional representability now.
* If G1 only needs the diagonal sentence plus unprovability from
  consistency, prefer using `PROV_HF_REPRESENTS_FWD` where possible.

Final wrapper:

`PROV_HF_REPRESENTS` is immediate once both directions exist.

## Group C — `hf_godel1.py`

### C1. Diagonal Function Package

Live stubs:

```text
DIAG_REPRESENTS
IS_FORM_DIAG_INTERNAL
FREE_IN_DIAG_INTERNAL
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
* `IS_FORM_DIAG_INTERNAL` and `FREE_IN_DIAG_INTERNAL` are structural
  body facts over the chosen `diag_internal` formula.

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

* Use `IS_FORM_DIAG_INTERNAL` and formula-constructor closure to prove
  the `is_form` conjunct.
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

Start with `SUBSTITUTE_REC_EMPTY`, `SUBSTITUTE_REC_VAR_HIT`, and
`SUBSTITUTE_REC_VAR_MISS`.

Reasons:

* They are the smallest current stubs.
* They exercise the same internal-body unfolding needed by every other
  `SUBSTITUTE_REC_*` theorem.
* They reduce the largest package stub, `HF_SYNTAX_REC_PACKAGE`, from a
  black box into a structural induction problem.

After those three pass, prove `SUBSTITUTE_REC_NOT`, then one binary case
such as `SUBSTITUTE_REC_INSERT`. Once those patterns are established,
the remaining constructor rules should be mostly mechanical.
