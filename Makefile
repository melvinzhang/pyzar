PY := uv run python

.PHONY: test

test:
	$(PY) fusion_test.py
	$(PY) tactics_test.py
	$(PY) classical.py
	$(PY) num.py
	$(PY) nat.py
	$(PY) parser.py
	$(PY) proof_test.py
