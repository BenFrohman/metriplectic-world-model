#!/usr/bin/env bash
# Author: Benjamin Stanley Frohman
# Truth Gate verification (see TRUTH_GATE.md). Fails on: sorry/admit/native_decide/axiom outside
# the draft directories, a missing or edited correspondence lock, a paper hash/quote mismatch,
# a failed lake build, nonstandard axioms in the locked theorems, a definitional (vacuous)
# correspondence, or a correspondence proof that leans on the main theorem.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p truth-gate-report
echo "== 1/4 static checks"
python3 scripts/truth_gate_check.py | tee truth-gate-report/static.txt
MOD=$(python3 -c "import json;print(json.load(open('TRUTH_GATE.lock'))['semantics_module'])")
echo "== 2/4 lake build (default targets)"
lake build 2>&1 | tee truth-gate-report/build.log
echo "== 3/4 lake build $MOD"
lake build "$MOD" 2>&1 | tee -a truth-gate-report/build.log
python3 - <<'PY'
import json, re, sys
lock = json.load(open("TRUTH_GATE.lock"))
drafts = [d.strip("/") for d in lock["draft_dirs"]]
bad = []
for line in open("truth-gate-report/build.log", encoding="utf-8", errors="replace"):
    if "declaration uses 'sorry'" in line:
        m = re.search(r"([\w./-]+\.lean)", line)
        f = m.group(1) if m else ""
        if not any(f == d or f.startswith(d + "/") or ("/" + d + "/") in f for d in drafts):
            bad.append(line.strip())
if bad:
    print("TRUTH GATE FAIL: sorry in build outside draft dirs:\n" + "\n".join(bad)); sys.exit(1)
print("build: no sorry outside draft dirs")
PY
echo "== 4/4 kernel audit of the lock (axioms, non-vacuity, transport)"
lake env lean scripts/TruthGateAudit.lean 2>&1 | tee truth-gate-report/audit.txt
grep -q 'TRUTH GATE AUDIT PASS' truth-gate-report/audit.txt
if grep -qE 'TRUTH GATE FAIL|error:|sorryAx' truth-gate-report/audit.txt; then exit 1; fi
sha256sum TRUTH_GATE.lock "$(python3 -c "import json;print(json.load(open('TRUTH_GATE.lock'))['semantics_file'])")" > truth-gate-report/sha256.txt
echo "TRUTH GATE PASS at $(git rev-parse HEAD 2>/dev/null || echo unknown)"
