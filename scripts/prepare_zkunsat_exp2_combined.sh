#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="${OUT_DIR:-$ROOT/artifacts/zkunsat-exp2-combined}"
SVCOMP_OUT="$OUT_DIR/svcomp"
STABLE_OUT="$OUT_DIR/stable"

python3 "$ROOT/scripts/prepare_zkunsat_exp2_svcomp.py" \
  --spec "$ROOT/benchmarks/zkunsat-exp2/svcomp_selected.csv" \
  --output-dir "$SVCOMP_OUT" \
  "$@"

python3 "$ROOT/scripts/prepare_zkunsat_exp2_stable.py" \
  --output-dir "$STABLE_OUT"

python3 - "$SVCOMP_OUT/manifest.csv" "$STABLE_OUT/manifest.csv" "$OUT_DIR/manifest.csv" <<'PY'
import csv
import sys
from pathlib import Path

inputs = [Path(sys.argv[1]), Path(sys.argv[2])]
output = Path(sys.argv[3])
rows = []
for path in inputs:
    with path.open(newline="") as f:
        for row in csv.DictReader(f):
            if row["expected_resolution_steps"]:
                rows.append(row)

rows.sort(key=lambda row: int(row["expected_resolution_steps"]))
output.parent.mkdir(parents=True, exist_ok=True)
with output.open("w", newline="") as f:
    writer = csv.DictWriter(f, fieldnames=rows[0].keys())
    writer.writeheader()
    writer.writerows(rows)
print(f"[combined] {output} rows={len(rows)}")
PY
