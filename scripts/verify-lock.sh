#!/usr/bin/env bash
# Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Benjamin Stanley Frohman
#
# Truth Gate verification (see TRUTH_GATE.md). Fails on: sorry/admit/native_decide/axiom outside
# the draft directories, a missing or edited correspondence lock, a paper hash/quote mismatch,
# a failed lake build, nonstandard axioms in the locked theorems, a definitional (vacuous)
# correspondence, a correspondence proof that leans on the main theorem, or a paper_claim that
# reuses repository Props instead of transcribing the paper (lock-form lint).
#
# Every phase runs, even after an earlier one fails, so the final verdict can say exactly which
# kind of failure happened. scripts/truth_gate_classify.py then sorts each failure into one class
# (KERNEL/PROOF, LOCK-FORM, PAPER-HASH, STALE-BASE) and prints the TRUTH GATE VERDICT block.
# Only KERNEL/PROOF is ever described as a proof failure.
set -uo pipefail
cd "$(dirname "$0")/.."
mkdir -p truth-gate-report
: > truth-gate-report/phases.tsv
rm -f truth-gate-report/lint.json truth-gate-report/classification.json
phase() { printf '%s\t%s\n' "$1" "$2" >> truth-gate-report/phases.tsv; }

echo "== 1/6 static lock checks (lock form, paper hash, forbidden tokens)"
python3 scripts/truth_gate_check.py > truth-gate-report/static.txt 2>&1; rc=$?
cat truth-gate-report/static.txt; phase static "$rc"

echo "== 2/6 lock-form lint (paper_claim must not reuse repository Props)"
python3 scripts/truth_gate_classify.py lint 2>&1 | tee truth-gate-report/lint.txt; phase lint "${PIPESTATUS[0]}"

MOD=$(python3 -c "import json;print(json.load(open('TRUTH_GATE.lock'))['semantics_module'])" 2>/dev/null || echo "")
echo "== 3/6 lake build (default targets)"
lake build 2>&1 | tee truth-gate-report/build.log; phase build "${PIPESTATUS[0]}"
if [ -n "$MOD" ]; then
  echo "== 4/6 lake build $MOD"
  lake build "$MOD" 2>&1 | tee truth-gate-report/build-semantics.log; phase build-semantics "${PIPESTATUS[0]}"
  cat truth-gate-report/build-semantics.log >> truth-gate-report/build.log
fi
python3 - <<'PY' > truth-gate-report/sorry.txt
import json, re
lock = json.load(open("TRUTH_GATE.lock"))
drafts = [d.strip("/") for d in lock["draft_dirs"]]
for line in open("truth-gate-report/build.log", encoding="utf-8", errors="replace"):
    if "declaration uses 'sorry'" in line:
        m = re.search(r"([\w./-]+\.lean)", line)
        f = m.group(1) if m else ""
        if not any(f == d or f.startswith(d + "/") or ("/" + d + "/") in f for d in drafts):
            print("sorry in build outside draft dirs: " + line.strip())
PY
if [ -s truth-gate-report/sorry.txt ]; then cat truth-gate-report/sorry.txt; phase sorry 1; else echo "build: no sorry outside draft dirs"; phase sorry 0; fi

echo "== 5/6 kernel audit of the lock (axioms, non-vacuity, transport)"
lake env lean scripts/TruthGateAudit.lean > truth-gate-report/audit.txt 2>&1
cat truth-gate-report/audit.txt
if grep -q 'TRUTH GATE AUDIT PASS' truth-gate-report/audit.txt && ! grep -qE 'TRUTH GATE FAIL|error:|sorryAx' truth-gate-report/audit.txt; then
  phase audit 0; else phase audit 1; fi

echo "== 6/6 additional locks (build, sorry scan, kernel audit)"
python3 - <<'PY2' > truth-gate-report/additional.txt
import json
for ex in json.load(open("TRUTH_GATE.lock")).get("additional_locks", []):
    print(ex["semantics_module"], ex["audit_file"])
PY2
i=0
while read -r XMOD XAUDIT; do
  [ -n "$XMOD" ] || continue
  i=$((i+1))
  echo "-- lake build $XMOD"
  lake build "$XMOD" > "truth-gate-report/build-additional-$i.log" 2>&1; brc=$?
  cat "truth-gate-report/build-additional-$i.log"; phase "build-additional-$i" "$brc"
  if grep -E "declaration uses 'sorry'" "truth-gate-report/build-additional-$i.log" | grep "$(echo "$XMOD" | tr . /)" > "truth-gate-report/sorry-additional-$i.txt"; then
    sed -i "s|^|sorry in $XMOD: |" "truth-gate-report/sorry-additional-$i.txt"; phase "sorry-additional-$i" 1
  else phase "sorry-additional-$i" 0; fi
  echo "-- kernel audit $XAUDIT"
  lake env lean "$XAUDIT" > "truth-gate-report/audit-additional-$i.txt" 2>&1
  cat "truth-gate-report/audit-additional-$i.txt"
  if grep -q 'TRUTH GATE AUDIT PASS' "truth-gate-report/audit-additional-$i.txt" && ! grep -qE 'TRUTH GATE FAIL|error:|sorryAx' "truth-gate-report/audit-additional-$i.txt"; then
    phase "audit-additional-$i" 0; else phase "audit-additional-$i" 1; fi
done < truth-gate-report/additional.txt
[ "$i" -gt 0 ] || echo "(none)"

sha256sum TRUTH_GATE.lock "$(python3 -c "import json;print(json.load(open('TRUTH_GATE.lock'))['semantics_file'])")" > truth-gate-report/sha256.txt 2>/dev/null || true
python3 scripts/truth_gate_classify.py report; rc=$?
if [ "$rc" -eq 0 ]; then
  echo "TRUTH GATE PASS at $(git rev-parse HEAD 2>/dev/null || echo unknown)"
fi
exit "$rc"
