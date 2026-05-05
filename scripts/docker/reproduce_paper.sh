#!/usr/bin/env bash
set -euo pipefail

ROOT="${ZK_PROVER_ROOT:-/workspace/zk-prover}"
ZKUNSAT_ROOT="${ZKUNSAT_ROOT:-/workspace/ZKUNSAT}"
ZKUNSAT_BIN="${ZKUNSAT_BIN:-$ZKUNSAT_ROOT/build/test}"
THREADS="${THREADS:-8}"
RUNS="${RUNS:-1}"

export ZKUNSAT_ROOT ZKUNSAT_BIN
export LOCAL_PREFIX="${LOCAL_PREFIX:-$ZKUNSAT_ROOT/.local}"
export CMAKE_PREFIX_PATH="${CMAKE_PREFIX_PATH:-$LOCAL_PREFIX}"
export CPATH="${CPATH:-$LOCAL_PREFIX/include:/usr/include/x86_64-linux-gnu}"
export LIBRARY_PATH="${LIBRARY_PATH:-$LOCAL_PREFIX/lib}"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-$LOCAL_PREFIX/lib}"
export PKG_CONFIG_PATH="${PKG_CONFIG_PATH:-$LOCAL_PREFIX/lib/pkgconfig}"

usage() {
  cat <<'EOF'
Usage: reproduce_paper.sh <command>

Commands:
  help          Show this message.
  smoke         Build-check the Rust workspace and run the smallest ZKUNSAT baseline instance.
  zkunsat-smoke Run only the smallest ZKUNSAT baseline instance.
  rq1           Reproduce Table 2 / RQ1 with scripts/run_rq1_bench.sh.
  rq1-smoke     Run the RQ1 pipeline without SP1 proof generation.
  rq2-prepare   Materialize the combined ZKUNSAT Exp2 manifest under artifacts/.
  rq2-smoke     Run the RQ2 runner on ZKUNSAT's smallest checked-in proof.
  rq2           Reproduce Table 3 / RQ2 with ZK-ProVer and ZKUNSAT.
  all           Run rq1 and rq2.

Useful environment:
  OUT_DIR       Artifact output directory.
  RUNS          Repetitions per fixture/backend, default 1.
  THREADS       Rayon and ZKUNSAT worker threads, default 8.
  RUN_ZKUNSAT_BUILD
                Set to 0 to use the ZKUNSAT binary already built into the image.
  P1_SKIP_PROVE Set to 1 for a fast Phase I smoke run.

For host persistence, run with:
  docker run --rm -v "$PWD/artifacts:/workspace/zk-prover/artifacts" zk-prover-paper:latest rq1-smoke
EOF
}

require_file() {
  local path="$1"
  if [[ ! -e "$path" ]]; then
    echo "missing required path: $path" >&2
    exit 1
  fi
}

run_zkunsat_smoke() {
  require_file "$ZKUNSAT_BIN"
  require_file "$ZKUNSAT_ROOT/prover_backend/example_small.prf.unfold"
  mkdir -p "$ZKUNSAT_ROOT/data"
  local port="${ZKUNSAT_SMOKE_PORT:-23456}"
  local log_dir="${OUT_DIR:-$ROOT/artifacts/docker-smoke}"
  mkdir -p "$log_dir"
  local party1_log="$log_dir/zkunsat_smoke_party1.log"
  local party2_log="$log_dir/zkunsat_smoke_party2.log"

  (
    cd "$ZKUNSAT_ROOT"
    ZKUNSAT_THREADS=1 "$ZKUNSAT_BIN" 1 "$port" 127.0.0.1 \
      prover_backend/example_small.prf.unfold >"$party1_log" 2>&1 &
    local party1=$!
    sleep 0.3
    ZKUNSAT_THREADS=1 "$ZKUNSAT_BIN" 2 "$port" 127.0.0.1 \
      prover_backend/example_small.prf.unfold >"$party2_log" 2>&1 &
    local party2=$!
    wait "$party1"
    wait "$party2"
  )

  grep -q -- "----end----" "$party1_log"
  grep -q -- "----end----" "$party2_log"
  echo "ZKUNSAT smoke logs written to $log_dir"
}

rq2_manifest_dir() {
  echo "${RQ2_PREP_DIR:-$ROOT/artifacts/zkunsat-exp2-combined}"
}

cmd="${1:-help}"
shift || true

cd "$ROOT"
case "$cmd" in
  help|-h|--help)
    usage
    ;;
  smoke)
    cargo check --workspace --all-targets --features proof-backends
    run_zkunsat_smoke
    ;;
  zkunsat-smoke)
    run_zkunsat_smoke
    ;;
  rq1)
    OUT_DIR="${OUT_DIR:-$ROOT/artifacts/docker-rq1}" RUNS="$RUNS" THREADS="$THREADS" \
      "$ROOT/scripts/run_rq1_bench.sh" "$@"
    ;;
  rq1-smoke)
    OUT_DIR="${OUT_DIR:-$ROOT/artifacts/docker-rq1-smoke}" RUNS="${RUNS:-1}" THREADS="$THREADS" \
      P1_SKIP_PROVE=1 "$ROOT/scripts/run_rq1_bench.sh" "$@"
    ;;
  rq2-prepare)
    OUT_DIR="$(rq2_manifest_dir)" \
      "$ROOT/scripts/prepare_zkunsat_exp2_combined.sh" "$@"
    ;;
  rq2-smoke)
    RUN_ZKUNSAT_BUILD="${RUN_ZKUNSAT_BUILD:-0}" \
      MANIFEST="${MANIFEST:-$ROOT/benchmarks/zkunsat-exp2/manifest.csv}" \
      OUT_DIR="${OUT_DIR:-$ROOT/artifacts/docker-rq2-smoke}" \
      RUNS="$RUNS" \
      THREADS="$THREADS" \
      "$ROOT/scripts/run_zkunsat_exp2.sh" --fixture "${FIXTURE:-zkunsat_example_small}" "$@"
    ;;
  rq2)
    if [[ -n "${MANIFEST:-}" ]]; then
      manifest="$MANIFEST"
    else
      prep_dir="$(rq2_manifest_dir)"
      OUT_DIR="$prep_dir" "$ROOT/scripts/prepare_zkunsat_exp2_combined.sh"
      manifest="$prep_dir/manifest.csv"
    fi
    RUN_ZKUNSAT_BUILD="${RUN_ZKUNSAT_BUILD:-0}" \
      MANIFEST="$manifest" \
      OUT_DIR="${OUT_DIR:-$ROOT/artifacts/docker-rq2}" \
      RUNS="$RUNS" \
      THREADS="$THREADS" \
      "$ROOT/scripts/run_zkunsat_exp2.sh" "$@"
    ;;
  all)
    "$0" rq1 "$@"
    "$0" rq2 "$@"
    ;;
  *)
    echo "unknown command: $cmd" >&2
    usage >&2
    exit 2
    ;;
esac
