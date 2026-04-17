#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE_ROOT="$(cd "$ROOT/.." && pwd)"
OUT_DIR="${OUT_DIR:-$ROOT/artifacts/unsat-scale-bench}"
GEN_DIR="${GEN_DIR:-$OUT_DIR/generated-fixtures}"
SIZES="${SIZES:-8,16,32,64}"
RUNS="${RUNS:-3}"
THREADS="${THREADS:-8}"
PICOSAT_BIN="${PICOSAT_BIN:-$ROOT/.cache/picosat-965/picosat}"
ZKUNSAT_ROOT="${ZKUNSAT_ROOT:-$WORKSPACE_ROOT/ZKUNSAT}"

mkdir -p "$OUT_DIR"

python3 "$ROOT/scripts/gen_range_pack_family.py" \
  --out-dir "$GEN_DIR" \
  --sizes "$SIZES"

fixture_args=()
IFS=',' read -r -a size_array <<< "$SIZES"
for size in "${size_array[@]}"; do
  size="${size// /}"
  [[ -n "$size" ]] || continue
  fixture_args+=(--fixture "range_pack_${size}_safe.c")
done

cd "$ROOT"
RAYON_NUM_THREADS="$THREADS" cargo run --release \
  --features proof-backends \
  --example bench_unsat_pipeline -- \
  --benchmark-root "$GEN_DIR" \
  --output-dir "$OUT_DIR" \
  --picosat "$PICOSAT_BIN" \
  --zkunsat-root "$ZKUNSAT_ROOT" \
  --zkunsat-threads "$THREADS" \
  --runs "$RUNS" \
  --skip-hyperplonk \
  "${fixture_args[@]}" \
  "$@"
