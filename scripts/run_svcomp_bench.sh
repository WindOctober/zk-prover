#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PICOSAT_BIN="${PICOSAT_BIN:-/tmp/picosat-965/picosat}"
OUT_DIR="${OUT_DIR:-$ROOT/artifacts/svcomp-pipeline-bench}"
THREADS="${THREADS:-8 16 32}"
RUNS="${RUNS:-3}"

cd "$ROOT"
for threads in $THREADS; do
  echo "== threads=$threads =="
  RAYON_NUM_THREADS="$threads" cargo run --release \
    --features proof-backends \
    --example bench_unsat_pipeline -- \
    --preset svcomp \
    --output-dir "$OUT_DIR" \
    --picosat "$PICOSAT_BIN" \
    --runs "$RUNS" \
    "$@"
done
