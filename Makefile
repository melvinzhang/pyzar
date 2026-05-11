SHELL := /bin/bash
PY := uv run python

LANDAU_GOLDEN := landau.golden
LANDAU_OUT    := landau.out
GODEL_GOLDEN  := godel.golden
GODEL_OUT     := godel.out

.PHONY: test test-kernel test-tactics test-parser test-axioms test-proof \
        test-theories test-prst test-golden update-golden lint flag-escapes \
        format clean

THEORY_FILES := classical.py num.py nat.py frac.py rat_int.py

# Layered test runner. Each layer depends only on the ones below it, so a
# failure at a lower layer makes upper-layer failures meaningless to debug.
# `make test` runs everything bottom-up; `make test-<layer>` runs one layer.

test: test-kernel test-tactics test-parser test-axioms test-proof \
      test-theories test-golden

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

# L6 -- theories
# Captures the printed `SATZ_N: |- ...` / `LEMMA: |- ...` lines from
# nat.py + frac.py + rat_int.py into $(LANDAU_OUT), and the same pattern
# from the godel stack into $(GODEL_OUT), for the golden checks below.
test-theories:
	$(PY) classical.py
	$(PY) tg_set_theory.py
	$(PY) num.py
	@set -o pipefail; \
	  raw=$$(mktemp); \
	  $(PY) nat.py | tee -a $$raw; \
	  $(PY) frac.py | tee -a $$raw; \
	  $(PY) rat_int.py | tee -a $$raw; \
	  grep -E '^[[:space:]]*[A-Z][A-Z0-9_]*[[:space:]]*:.*\|-' $$raw > $(LANDAU_OUT); \
	  rm -f $$raw
	@set -o pipefail; \
	  raw=$$(mktemp); \
	  $(PY) nat0.py | tee -a $$raw; \
	  $(PY) nat0_order.py | tee -a $$raw; \
	  $(PY) bits.py | tee -a $$raw; \
	  $(PY) hf_sets.py | tee -a $$raw; \
	  $(PY) hf_syntax.py | tee -a $$raw; \
	  $(PY) hf_connectives.py | tee -a $$raw; \
	  $(PY) hf_proof.py | tee -a $$raw; \
	  $(PY) hf_repr_core.py | tee -a $$raw; \
	  $(PY) hf_logic.py | tee -a $$raw; \
	  $(PY) hf_repr_thms.py | tee -a $$raw; \
	  $(PY) hf_godel1.py | tee -a $$raw; \
	  grep -E '^[[:space:]]*[A-Z][A-Z0-9_]*[[:space:]]*:.*\|-' $$raw > $(GODEL_OUT); \
	  rm -f $$raw

# PRST stack -- run each module in dependency order. Sketch-level
# (stubs throughout) so we just confirm everything loads and the
# __main__ smoke-prints succeed.
test-prst:
	$(PY) prst_syntax.py
	$(PY) prst_connectives.py
	$(PY) prst_pr.py
	$(PY) prst_proof.py
	$(PY) prst_repr.py
	$(PY) prst_godel1.py
	$(PY) prst_godel2.py

# L7 -- golden: every theorem's pp(concl) matches the checked-in
# `landau.golden`.  The kernel certifies inferences but cannot tell whether
# the stated goal is what Landau actually wrote, so this layer locks down
# the statements against silent drift across refactors.  Run after a
# reviewed transcription audit; regenerate via `make update-golden` when a
# statement change is intentional.
test-golden: test-theories
	@status=0; \
	if diff -u $(LANDAU_GOLDEN) $(LANDAU_OUT); then \
	  echo "Landau golden OK ($$(wc -l < $(LANDAU_GOLDEN)) theorems)."; \
	else \
	  echo ""; \
	  echo "Landau golden mismatch -- inspect the diff above."; \
	  status=1; \
	fi; \
	if diff -u $(GODEL_GOLDEN) $(GODEL_OUT); then \
	  echo "Goedel golden OK ($$(wc -l < $(GODEL_GOLDEN)) theorems)."; \
	else \
	  echo ""; \
	  echo "Goedel golden mismatch -- inspect the diff above."; \
	  status=1; \
	fi; \
	if [ $$status -ne 0 ]; then \
	  echo "If the new statements are intentional, run: make update-golden"; \
	  exit 1; \
	fi

# Regenerate the golden snapshots after an intentional statement change.
# Requires test-theories to have produced fresh $(LANDAU_OUT)/$(GODEL_OUT).
update-golden: test-theories
	@cp $(LANDAU_OUT) $(LANDAU_GOLDEN)
	@echo "Updated $(LANDAU_GOLDEN) ($$(wc -l < $(LANDAU_GOLDEN)) theorems)."
	@cp $(GODEL_OUT) $(GODEL_GOLDEN)
	@echo "Updated $(GODEL_GOLDEN) ($$(wc -l < $(GODEL_GOLDEN)) theorems)."

# Style lint via ruff (unused imports, formatting drift, etc.).
lint:
	uv run ruff check

# Flag non-declarative patterns inside @proof bodies. Two kinds:
#   - ESCAPE: a direct kernel/tactic call (REFL/TRANS/MK_COMB/SPEC/MP/...).
#   - PROCEDURAL: an assignment ``name = ...`` whose RHS constructs a
#     theorem; the binding hides the conclusion from the source. Reported
#     as ``PROC:<rule>``. Inner escapes inside a procedural RHS are
#     suppressed to avoid double-counting.
# Exits non-zero if any offender remains; not part of `make test` while
# the existing escape hatches (e.g. MK_DEST/DEST_MK peels) still need
# landing.
flag-escapes:
	$(PY) lint_declarative.py $(THEORY_FILES)

# Format the codebase in place with ruff format.
format:
	uv run ruff format

clean:
	rm -f $(LANDAU_OUT) $(GODEL_OUT)
