# Declarative form for `num.py`

`nat.py` and `num.py` are now entirely `@proof`. The classical logic proofs
live in `classical.py` (above `proof.py` in the import graph) and are
declarative including the polymorphic quantifier-negation rules; the Peano
construction and recursion theorem in `num.py` are declarative on top of
inline parser registrations and the rewriter's binder-aware descent. This
doc records the cluster, the shipped DSL primitives that made each port
possible, and the two cross-cutting wishes that remain open.

## What's in scope

| File / proof                          | Lines | Style today          | Verdict |
|---------------------------------------|-------|----------------------|---------|
| `F_NEQ_T` (`classical.py`)            |   3   | declarative          | ✅ shipped as `@proof` |
| `EXCLUDED_MIDDLE` (`classical.py`)    |   ~30 | declarative + 10-line kernel sub-proof | ✅ shipped as `@proof` |
| `NOT_NOT_ELIM` (`classical.py`)       |   ~10 | universal `@proof` + 2-line wrapper | ✅ shipped |
| `NOT_EX_TO_FORALL_NOT` (rule)         |   ~7  | parametric           | ✅ shipped as polymorphic `@proof` + thin `SPEC`+`MP` wrapper |
| `NOT_FORALL_TO_EX_NOT` (rule)         |   ~12 | parametric, classical| ✅ shipped as polymorphic `@proof` + thin `SPEC`+`MP` wrapper |
| `_prove_ind_suc_props`                |   ~30 | uses `ELIM_EX`       | ✅ ported as `_IND_SUC_PROPS_PAIR` (4-line `@proof` + `CONJUNCT1`/`2`) |
| `_prove_exists_witness`               |   ~60 | nested `ELIM_EX`     | ✅ ported as `_EXISTS_WITNESS` (`@proof`, ~12 lines) |
| `_prove_ind_suc_neq_ind_1`            |   ~30 | substitution dance   | ✅ ported as `IND_SUC_NEQ_IND_1` (3-line `@proof` after Abs-descent in `REWRITE`) |
| `NUM_REP_IND_1` / `_IND_SUC_CLOSED`   |   ~25 | wrap/unwrap NUM_REP  | ✅ ported as `@proof` (uses `p.unfold` + nested `proof()`) |
| `NUM_REP_dest_num`                    |   ~15 | small               | ✅ ported as `@proof` |
| `AXIOM_3` / `AXIOM_4`                 |   ~30 | unfold + peel        | ✅ ported as `@proof` (declarative outer + kernel peel inner) |
| `INDUCTION`                           |   ~90 | predicate `Q` Abs    | ✅ ported as `@proof` (single-arg `p.let("Q(i:ind) := ...")` + `by_select`) |
| `R_AT_1` / `R_STEP`                   |   ~30 | builds `R c h n m`   | ✅ ported as `@proof` (4-arg `p.let("R(c,h,n,m) := ...")`) |
| `R_UNIQUE_BASE` / `_STEP`             |   ~280| `Qp`-acrobatics      | ✅ ported as `@proof` (multi-arg lets for `R` and `Qp(k,a)`) |
| `NUM_RECURSION`                       |   ~120| chains `@m. R c h n m` | ✅ ported as `@proof` (R let + kernel SELECT-witness chain) |

---

## ✅ `F_NEQ_T`

Three-line `@proof` in `classical.py`:

```python
@proof
def F_NEQ_T(p):
    p.goal("~(F = T)")
    with p.suppose("h: F = T"):
        p.absurd().by_thm(EQ_MP(SYM(p.fact("h")), TRUTH))
```

---

## ✅ `NOT_NOT_ELIM` — universal `@proof` + thin wrapper

The procedural rule used to take `|- ~~p` and return `|- p` directly.
Refactored shape: prove the *universal* form once, then `SPEC` + `MP` at
call sites:

```python
@proof
def NOT_NOT_ELIM_AX(p):
    p.goal("!q:bool. ~~q ==> q")
    p.fix("q")
    p.assume("hnn: ~~q")
    with p.cases_on(EXCLUDED_MIDDLE, "q"):
        with p.case("hq: q"):
            p.thus("q").by_thm(p.fact("hq"))
        with p.case("hnq: ~q"):
            p.absurd().by_conj("hnq", "hnn")

def NOT_NOT_ELIM(th):
    p_t = rand(rand(th._concl))
    return MP(SPEC(p_t, NOT_NOT_ELIM_AX), th)
```

Net win: declarative content, procedural surface.

---

## ✅ `NOT_EX_TO_FORALL_NOT` / `NOT_FORALL_TO_EX_NOT`

Universal-form theorems live in `classical.py`:

  * `NOT_EX_TO_FORALL_NOT_AX : |- !p. ~(?v:A. p v) ==> !v:A. ~(p v)`
  * `NOT_FORALL_TO_EX_NOT_AX : |- !p. ~(!v:A. p v) ==> ?v:A. ~(p v)`

Both are declarative `@proof` blocks parameterised over the predicate's
type variable via `types={"p": _pred_ty, "A": aty}`. The rule wrappers
collapse to a one-liner: `MP(BETA_RULE(SPEC(pred, INST_TYPE(...))), th)`.
Same shape as `NOT_NOT_ELIM`.

---

## ✅ `EXCLUDED_MIDDLE` (Diaconescu)

The proof introduces `U := \x. (x=F) \/ t` and `V := \x. (x=T) \/ t`,
applies `SELECT_AX` to extract `(@U = F) \/ t` and `(@V = T) \/ t`, then
case-splits over both with the cross-case using function extensionality
to derive `F = T` (contradicting `F_NEQ_T`).

The shipped proof is ~30 lines `@proof` plus a ~10-line kernel helper
(`_diaconescu_F_eq_T`) for the cross-case derivation — about 1/3 the
original procedural size.

Primitives used:

- `p.let("M(x:bool) := …")` — typed bvars supported.
- `p.have(...).by_select(axiom, *args)` — materializes a let as a kernel
  `Abs`, `SPEC`s the HO axiom at it, `BETA_RULE`s, resolves remaining
  args as fact `MP`s or term `SPEC`s.
- `by_disj` — auto-`DISJ1`/`DISJ2` pick for matching sub-equations.

---

## ✅ Peano construction (`_IND_SUC_PROPS_PAIR`, `_EXISTS_WITNESS`, `IND_SUC_NEQ_IND_1`, `NUM_REP_*`, `AXIOM_3/4`)

All of these `@proof` blocks live between the relevant `*_DEF` and the
parser registrations of the new constants in `num.py`. The pattern
across the cluster:

* **`_IND_SUC_PROPS_PAIR`** — `prf.choose` the witness from `INFINITY_AX`,
  `by_rewrite_of` to fold the `@`-witness back to `IND_SUC` via
  `SYM(IND_SUC_DEF)`. Two `CONJUNCT*` extractions yield
  `ONE_ONE_IND_SUC` and `NOT_ONTO_IND_SUC`. ~4 lines of `@proof`.
* **`_EXISTS_WITNESS`** — unfold `~(ONTO IND_SUC)` once at module scope
  via `UNFOLD`, apply `NOT_FORALL_TO_EX_NOT`, `prf.choose` the outer
  witness, `NOT_EX_TO_FORALL_NOT` + `NE_SYM` to flip the inner equation,
  `by_witness` to re-introduce the existential. ~12 lines of `@proof`.
* **`IND_SUC_NEQ_IND_1`** — `prf.choose("z: …", from_=_EXISTS_WITNESS)`,
  then a single `by_rewrite_of("z_eq", [SYM(IND_1_DEF)])` — the rewrite
  engine descends into `Abs` bodies (closed rules only; rules with
  hypotheses stay top-level to avoid capture-driven loops on auto-choose
  facts). ~3 lines.
* **`NUM_REP_IND_1`, `NUM_REP_IND_SUC_CLOSED`, `NUM_REP_dest_num`,
  `AXIOM_3`, `AXIOM_4`** — `p.unfold` to expose the definitional body,
  declarative sub-proofs, `by_eq_mp` / `by_rewrite_of` to refold.
* **`INDUCTION`** — `p.let("Q(i:ind) := NUM_REP i /\ P (mk_num i)")`
  introduces the predicate; `by_select` materializes it for the HO
  application of `NUM_REP_unfold`.
* **`R_AT_1` / `R_STEP` / `R_UNIQUE_*` / `NUM_RECURSION`** — multi-arg
  `p.let("R(c, h, n, m) := !Q. …")` and `p.let("Qp(k, a) := …")` make
  the closure-style HO induction read directly. The boundary still
  needs a `BETA_RULE` per HO-lemma application; let-substitution
  carries everywhere else.

Required infrastructure (all shipped):

- `p.unfold` / module-level `tactics.UNFOLD`.
- `p.choose` with auto-`@` witness; `by_witness`.
- `NOT_FORALL_TO_EX_NOT` / `NOT_EX_TO_FORALL_NOT` (now polymorphic).
- Inline parser registrations of `IND_SUC` / `IND_1` / `NUM_REP` / `1`
  / `SUC` / etc. so each `@proof` block can mention surface names
  immediately after the definition introduces them.
- Multi-arg `p.let` with capture-avoiding substitution.
- `_Have.by_select` for HO-to-1st-order boundary.
- Abs-descent in `REWRITE_CONV` (with empty-asl filter under binders).

---

## Cross-cutting wishes

1. ✅ **`p.unfold(def_th, *args)`** — variadic helper for
   `BETA_RULE(AP_THM(D, t))`. Shipped as `tactics.UNFOLD` (kernel-term
   args) and `Proof.unfold` (parses string args in current scope).
   `_binop_unfold` deleted.

2. ✅ **`_Have.by_select(axiom, *args)`** — HO-to-1st-order boundary
   helper. Now (post-Isabelle migration) `SPEC`s the HO axiom at the
   lazy-let carrier `Var` directly; no Abs materialization, no
   `BETA_RULE`. Resolves remaining args as fact `MP`s (with conversion-
   on-match for folded/unfolded mismatch) or term `SPEC`s.

3. ✅ **Multi-arg `p.let`** (Isabelle-style). Comma-separated arg list
   with optional per-arg type annotations. The let registers a fresh
   kernel `Var` carrier plus a local equation
   `[!args. R args = body] |- !args. R args = body`; goals and facts
   stay folded. The hypothesis is discharged on frame close (carrier
   substituted with `\args. body`, BETA-normalized). See
   `unfold_at_use.md` for the migration history.

4. ✅ **Polymorphic `@proof` blocks**. `goal(spec, types={"A": aty,
   ...})` registers tyvar bindings; the parser's binder annotation
   grammar (`!v:A. body`) resolves the type name through both the
   registered `Signature` and any env-provided `Tyvar`/`Tyapp`. The
   resulting theorem is naturally polymorphic in `A`. See
   `NOT_EX_TO_FORALL_NOT_AX` / `NOT_FORALL_TO_EX_NOT_AX` for the
   worked-example form.

5. ✅ **Lazy `p.let`** (was: "auto-unfold registered definitions").
   Resolved by switching `p.let` to Isabelle-style mechanics: the
   carrier stays folded, downstream tactics consult the local equation
   via conversion-on-match (`_match_modulo_lazy_lets`), the hypothesis
   is discharged on frame close. Removes the prior carrier-vs-sugar
   dilemma — there is no "eager / always unfold" mode anymore.
   `define()` (module-scope constants) remains opaque, with explicit
   `p.unfold` / `UNFOLD` for use-site unfolds. The few module-scope
   `BETA_RULE(AP_THM(D, t))` chains (`_NOT_ONTO_UNFOLD`,
   `_NUM_REP_unfold`) still exist by design — a `define(simp=True)`
   tag mirroring Isabelle's `[simp]` is parked as a stretch goal.

### Open

6. 🟡 **`p.split_conj` for goals**. Today `split_conj` only takes
   conjunction-shaped facts apart; goals of shape `A /\ B` must be
   handled with two `p.have` plus a final `CONJ`. Auto-splitting the
   goal would shave a few lines from `R_UNIQUE_BASE` / `R_UNIQUE_STEP`.
   Minor — the workaround is fine.

---

## Import-order resolution (historical)

The classical proofs were unblocked by extracting them into
`classical.py`. The `num.py` ports were unblocked by:

1. **`proof.py`'s `from num import ...` is lazy** (deferred to the call
   sites of `induction()` / `base()` / `step()` / the `_InductionCtx`
   exit). That makes the `from proof import proof` at the top of
   `num.py` cycle-free in practice.

2. **Parser registrations are inline** as each constant becomes
   available: `add_type("ind", ind_ty)` and `add_const("IND_SUC", ...)`
   (and the ind-instantiations of `ONE_ONE` / `ONTO`) happen right after
   `IND_SUC_DEF`; `add_const("IND_1", ...)` after `IND_1_DEF`;
   `add_const("NUM_REP", ...)` after `NUM_REP_DEF`; the `num` type,
   `mk_num` / `dest_num` / `1` / `SUC` / `default_var_ty = num_ty`
   registrations happen as those constants come into scope.

The dependency graph is unchanged:

```
fusion ─► axioms ─► tactics ─► parser ─► proof ─► classical ─► num ─► nat
```
