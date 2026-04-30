PY := uv run python

.PHONY: test

test:
	$(PY) fusion_test.py
	$(PY) logic.py
	$(PY) num.py
	$(PY) nat.py
	$(PY) parser.py
