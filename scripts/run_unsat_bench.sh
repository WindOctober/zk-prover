#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE_ROOT="$(cd "$ROOT/.." && pwd)"
PICOSAT_ROOT="${PICOSAT_ROOT:-$ROOT/.cache/picosat-965}"
PICOSAT_BIN="${PICOSAT_BIN:-$PICOSAT_ROOT/picosat}"
ZKUNSAT_ROOT="${ZKUNSAT_ROOT:-$WORKSPACE_ROOT/ZKUNSAT}"
OUT_DIR="${OUT_DIR:-$ROOT/artifacts/unsat-bench}"
THREADS="${THREADS:-8 16 32}"
RUNS="${RUNS:-3}"

build_picosat() {
  if [[ -x "$PICOSAT_BIN" ]]; then
    return
  fi

  local extracted_root="$ROOT/.cache/picosat-965"
  mkdir -p "$ROOT/.cache"
  rm -rf "$PICOSAT_ROOT"
  curl -L https://fmv.jku.at/picosat/picosat-965.tar.gz | tar xz -C "$ROOT/.cache"
  if [[ "$extracted_root" != "$PICOSAT_ROOT" ]]; then
    mv "$extracted_root" "$PICOSAT_ROOT"
  fi
  (
    cd "$PICOSAT_ROOT"
    make clean >/dev/null 2>&1 || true
    ./configure.sh -t
    make -j"$(nproc)"
  )
}

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

build_picosat
build_zkunsat

cd "$ROOT"
for threads in $THREADS; do
  echo "== threads=$threads =="
  RAYON_NUM_THREADS="$threads" cargo run --release \
    --features proof-backends \
    --example bench_unsat_pipeline -- \
    --preset synthetic-unsat \
    --output-dir "$OUT_DIR" \
    --picosat "$PICOSAT_BIN" \
    --runs "$RUNS" \
    --zkunsat-root "$ZKUNSAT_ROOT" \
    --zkunsat-threads "$threads" \
    "$@"
done
