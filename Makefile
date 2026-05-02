PY := uv run python

.PHONY: test test-kernel test-tactics test-parser test-axioms test-proof test-theories

# Layered test runner. Each layer depends only on the ones below it, so a
# failure at a lower layer makes upper-layer failures meaningless to debug.
# `make test` runs everything bottom-up; `make test-<layer>` runs one layer.

test: test-kernel test-tactics test-parser test-axioms test-proof test-theories

# L1 -- kernel: fusion (terms, types, primitive inference rules).
test-kernel:
	$(PY) fusion_test.py

# L2 -- tactics: derived rules built on the kernel (SPEC, GEN, REWRITE, ...).
test-tactics:
	$(PY) tactics_test.py

# L3 -- surface syntax: Lark grammar, label/let-spec parsers, pp.
test-parser:
	$(PY) parser_test.py

# L4 -- axioms: HOL Light boolean definitions and the 3 axioms.
test-axioms:
	$(PY) axioms_test.py

# L5 -- proof DSL: have/thus, by/by_match, induction, choose, lazy lets.
test-proof:
	$(PY) proof_test.py

# L6 -- theories: classical logic, then the Landau development bottom-up
# (num builds the natural numbers; nat proves Landau's Sätze on them; frac
# builds rationals on top of nat).
test-theories:
	$(PY) classical.py
	$(PY) num.py
	$(PY) nat.py
	$(PY) frac.py
