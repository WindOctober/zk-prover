#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PICOSAT_ROOT="${PICOSAT_ROOT:-$ROOT/.cache/picosat-965}"
PICOSAT_BIN="${PICOSAT_BIN:-$PICOSAT_ROOT/picosat}"
OUT_DIR="${OUT_DIR:-$ROOT/artifacts/rq1-$(date +%Y%m%d-%H%M%S)}"
if [[ "$OUT_DIR" != /* ]]; then
  OUT_DIR="$ROOT/$OUT_DIR"
fi
RUNS="${RUNS:-1}"
THREADS="${THREADS:-32}"
P1_SKIP_PROVE="${P1_SKIP_PROVE:-0}"
P1_PROOF_ONLY="${P1_PROOF_ONLY:-1}"
P1_SHARD_SIZE="${P1_SHARD_SIZE:-}"
CONTINUE_ON_P1_ERROR="${CONTINUE_ON_P1_ERROR:-1}"
RUN_PHASE1="${RUN_PHASE1:-1}"
RUN_PHASE2="${RUN_PHASE2:-1}"

OFFICIAL_FIXTURES=(
  "vendor/sv-benchmarks/c/validation-crafted/if.c"
  "vendor/sv-benchmarks/c/validation-crafted/ternary.c"
)

SYNTHETIC_UNSAT_FIXTURES=(
  "synthetic-c/validation-crafted/diamond_safe.c"
  "synthetic-c/validation-crafted/range_arith_safe.c"
  "synthetic-c/validation-crafted/branch_sum_safe.c"
  "synthetic-c/validation-crafted/nested_guard_safe.c"
  "synthetic-c/validation-crafted/range_pack_2_safe.c"
)

UNROLLED_UNSAT_FIXTURES=(
  "svcomp-unrolled/loop-invgen/down_3_unrolled.c"
  "svcomp-unrolled/loop-invgen/large_const_2_unrolled.c"
)

UNROLLED_SAT_FIXTURES=(
  "svcomp-unrolled/loop-lit/bhmr2007_3_bug_unrolled.c"
)

build_picosat() {
  if [[ -x "$PICOSAT_BIN" ]]; then
    return
  fi

  mkdir -p "$ROOT/.cache"
  rm -rf "$PICOSAT_ROOT"
  curl -L https://fmv.jku.at/picosat/picosat-965.tar.gz | tar xz -C "$ROOT/.cache"
  if [[ "$ROOT/.cache/picosat-965" != "$PICOSAT_ROOT" ]]; then
    mv "$ROOT/.cache/picosat-965" "$PICOSAT_ROOT"
  fi
  (
    cd "$PICOSAT_ROOT"
    make clean >/dev/null 2>&1 || true
    ./configure.sh -t
    make -j"$(nproc)"
  )
}

run_phase1_group() {
  local output="$1"
  local benchmark_root="$2"
  shift 2
  local skip_args=()
  if [[ "$P1_SKIP_PROVE" == "1" ]]; then
    skip_args+=(--skip-prove)
  fi
  if [[ "$P1_PROOF_ONLY" == "1" ]]; then
    skip_args+=(--proof-only)
  fi
  local env_args=()
  if [[ -n "$P1_SHARD_SIZE" ]]; then
    env_args+=(SHARD_SIZE="$P1_SHARD_SIZE")
  fi
  echo "== Phase I -> $output =="
  : >"$output"
  : >"$output.failures"
  local wrote_header=0
  local fixture=""
  while (($#)); do
    if [[ "$1" != "--fixture" ]]; then
      echo "unexpected Phase I argument: $1" >&2
      exit 2
    fi
    fixture="$2"
    shift 2

    local temp_output="$output.tmp"
    if ! env "${env_args[@]}" cargo run -p zk-prover-frontend-runner --release -- \
      --repeat "$RUNS" \
      --benchmark-root "$benchmark_root" \
      "${skip_args[@]}" \
      --fixture "$fixture" >"$temp_output"; then
      echo "$fixture" >>"$output.failures"
      rm -f "$temp_output"
      if [[ "$CONTINUE_ON_P1_ERROR" == "1" ]]; then
        echo "[WARN] Phase I failed for $fixture; continuing" >&2
        continue
      fi
      exit 1
    fi

    if [[ "$wrote_header" == "0" ]]; then
      cat "$temp_output" >>"$output"
      wrote_header=1
    else
      tail -n +2 "$temp_output" >>"$output"
    fi
    rm -f "$temp_output"
  done
}

run_phase2_sat() {
  local output="$1"
  local benchmark_root="$2"
  shift 2
  echo "== Phase II SAT -> $output =="
  RAYON_NUM_THREADS="$THREADS" cargo run --release \
    --features backend-solver,backend-plonky3 \
    --example bench_phase2_sat -- \
    --benchmark-root "$benchmark_root" \
    --runs "$RUNS" \
    "$@" >"$output"
}

run_phase2_unsat() {
  local output_dir="$1"
  local benchmark_root="$2"
  shift 2
  echo "== Phase II UNSAT -> $output_dir =="
  RAYON_NUM_THREADS="$THREADS" cargo run --release \
    --features proof-backends \
    --example bench_unsat_pipeline -- \
    --preset synthetic-unsat \
    --benchmark-root "$benchmark_root" \
    --output-dir "$output_dir" \
    --picosat "$PICOSAT_BIN" \
    --runs "$RUNS" \
    --skip-hyperplonk \
    --skip-zkunsat \
    --check-formula-commitment \
    "$@"
}

main() {
  mkdir -p "$OUT_DIR"
  build_picosat
  cd "$ROOT"

  local official_args=()
  local fixture
  for fixture in "${OFFICIAL_FIXTURES[@]}"; do
    official_args+=(--fixture "$fixture")
  done

  local synthetic_args=()
  for fixture in "${SYNTHETIC_UNSAT_FIXTURES[@]}"; do
    synthetic_args+=(--fixture "$fixture")
  done

  local unrolled_args=()
  for fixture in "${UNROLLED_UNSAT_FIXTURES[@]}" "${UNROLLED_SAT_FIXTURES[@]}"; do
    unrolled_args+=(--fixture "$fixture")
  done

  local unrolled_sat_args=()
  for fixture in "${UNROLLED_SAT_FIXTURES[@]}"; do
    unrolled_sat_args+=(--fixture "$fixture")
  done

  local unrolled_unsat_args=()
  for fixture in "${UNROLLED_UNSAT_FIXTURES[@]}"; do
    unrolled_unsat_args+=(--fixture "$fixture")
  done

  if [[ "$RUN_PHASE1" == "1" ]]; then
    run_phase1_group \
      "$OUT_DIR/phase1_official.csv" \
      "$ROOT/benchmarks/svcomp-initial" \
      "${official_args[@]}"
    run_phase1_group \
      "$OUT_DIR/phase1_synthetic.csv" \
      "$ROOT/tests/fixtures" \
      "${synthetic_args[@]}"
    run_phase1_group \
      "$OUT_DIR/phase1_unrolled.csv" \
      "$ROOT/tests/fixtures" \
      "${unrolled_args[@]}"
  fi

  if [[ "$RUN_PHASE2" == "1" ]]; then
    run_phase2_sat \
      "$OUT_DIR/phase2_sat_official.csv" \
      "$ROOT/benchmarks/svcomp-initial" \
      "${official_args[@]}"
    run_phase2_sat \
      "$OUT_DIR/phase2_sat_unrolled.csv" \
      "$ROOT/tests/fixtures" \
      "${unrolled_sat_args[@]}"

    run_phase2_unsat \
      "$OUT_DIR/phase2_synthetic" \
      "$ROOT/tests/fixtures" \
      "${synthetic_args[@]}"
    run_phase2_unsat \
      "$OUT_DIR/phase2_unrolled" \
      "$ROOT/tests/fixtures" \
      "${unrolled_unsat_args[@]}"
  fi

  python3 "$ROOT/scripts/format_rq1_results.py" \
    --out-dir "$OUT_DIR" \
    --threads "$THREADS"

  echo "RQ1 artifacts written to $OUT_DIR"
}

main "$@"
