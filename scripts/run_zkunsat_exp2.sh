#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE_ROOT="$(cd "$ROOT/.." && pwd)"
ZKUNSAT_ROOT="${ZKUNSAT_ROOT:-$WORKSPACE_ROOT/ZKUNSAT}"
ZKUNSAT_BIN="${ZKUNSAT_BIN:-$ZKUNSAT_ROOT/build/test}"
OUT_DIR="${OUT_DIR:-$ROOT/artifacts/zkunsat-exp2}"
THREADS="${THREADS:-8}"
RUNS="${RUNS:-1}"
MANIFEST="${MANIFEST:-$ROOT/benchmarks/zkunsat-exp2/manifest.csv}"
RUN_ZKUNSAT_BUILD="${RUN_ZKUNSAT_BUILD:-1}"
ZK_PROVER_FRI_LOG_BLOWUP="${ZK_PROVER_FRI_LOG_BLOWUP:-4}"
ZK_PROVER_FRI_NUM_QUERIES="${ZK_PROVER_FRI_NUM_QUERIES:-20}"

build_zkunsat() {
  local local_prefix="$ZKUNSAT_ROOT/.local"
  (
    cd "$ZKUNSAT_ROOT"
    export LOCAL_PREFIX="$local_prefix"
    export CMAKE_PREFIX_PATH="$local_prefix${CMAKE_PREFIX_PATH:+:$CMAKE_PREFIX_PATH}"
    export CPATH="$local_prefix/include:/usr/include/x86_64-linux-gnu${CPATH:+:$CPATH}"
    export LIBRARY_PATH="$local_prefix/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
    export LD_LIBRARY_PATH="$local_prefix/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
    cmake -S . -B build
    cmake --build build -j"$(nproc)"
  )
}

if [[ "$RUN_ZKUNSAT_BUILD" == "1" ]]; then
  build_zkunsat
fi

cd "$ROOT"
RAYON_NUM_THREADS="$THREADS" \
ZKUNSAT_THREADS="$THREADS" \
ZKUNSAT_ROOT="$ZKUNSAT_ROOT" \
ZKUNSAT_BIN="$ZKUNSAT_BIN" \
ZK_PROVER_FRI_LOG_BLOWUP="$ZK_PROVER_FRI_LOG_BLOWUP" \
ZK_PROVER_FRI_NUM_QUERIES="$ZK_PROVER_FRI_NUM_QUERIES" \
cargo run --release \
  --features backend-plonky3 \
  --example bench_zkunsat_exp2 -- \
  --manifest "$MANIFEST" \
  --output-dir "$OUT_DIR" \
  --runs "$RUNS" \
  --zkunsat-root "$ZKUNSAT_ROOT" \
  --zkunsat-bin "$ZKUNSAT_BIN" \
  --zkunsat-threads "$THREADS" \
  "$@"
