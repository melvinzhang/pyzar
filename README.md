# pyzar

A small HOL Light–style proof kernel in Python, used to formalise Edmund
Landau's *Grundlagen der Analysis* from the Peano axioms.

The kernel is faithful to `hol-light/fusion.ml`: 10 primitive inference
rules, 3 logical axioms (ETA, SELECT, INFINITY), and nothing else. Every
theorem in the development is built on top of that kernel.

## Layout

The codebase is layered; each file depends only on the ones above it.

- [`fusion.py`](fusion.py): Kernel: types, terms, primitive inference rules
- [`basics.py`](basics.py): Derived term/type syntax: `mk_eq`, `mk_app`, `rator`/`rand`, binop/unop/binder helpers
- [`tactics.py`](tactics.py): Derived rules: SPEC, GEN, REWRITE, …
- [`parser.py`](parser.py): Lark grammar, label/let-spec parsers, pretty printer
- [`axioms.py`](axioms.py): Boolean definitions + the 3 axioms
- [`proof.py`](proof.py): Proof DSL: `have`/`thus`, `by`/`by_match`, induction, choose
- [`classical.py`](classical.py): Classical logic (Diaconescu's EM)
- [`num.py`](num.py): Naturals carved from `ind`; Peano 3/4/5 as theorems; `INDUCT`, `NUM_RECURSION`
- [`nat.py`](nat.py): Landau Kapitel 1: addition, order, multiplication (Sätze 1–36)
- [`frac.py`](frac.py): Landau Kapitel 2 §§1–4: fractions (Sätze 37–77)
- [`landau.golden`](landau.golden): Pinned `pp(concl)` of every Satz/Axiom — locks statements against drift

## Running

```bash
make test            # all layers, bottom-up
make test-kernel     # just one layer
make test-golden     # ensure we are proving Landau's theorems
```

`make test-theories` runs `nat.py` and `frac.py`, capturing each
`SATZ_N: |- …` line into `landau.out`. `make test-golden` then diffs
that against `landau.golden`. The kernel certifies inferences but
cannot tell whether the stated goal is what Landau actually wrote;
the golden layer is what locks the *statements* down.

## Requires

* Python ≥ 3.12
* [`uv`](https://docs.astral.sh/uv/)
* GNU Make
