#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE_ROOT="$(cd "$ROOT/.." && pwd)"
OUT_DIR="${OUT_DIR:-$ROOT/artifacts/zkunsat-exp2-svcomp}"
ZKUNSAT_ROOT="${ZKUNSAT_ROOT:-$WORKSPACE_ROOT/ZKUNSAT}"
PICOSAT="${PICOSAT:-$ROOT/.cache/picosat-965/picosat}"

python3 "$ROOT/scripts/prepare_zkunsat_exp2_svcomp.py" \
  --output-dir "$OUT_DIR" \
  --picosat "$PICOSAT" \
  --zkunsat-root "$ZKUNSAT_ROOT" \
  "$@"
