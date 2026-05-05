#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
IMAGE="${IMAGE:-zk-prover-paper:latest}"

docker build \
  --tag "$IMAGE" \
  "$@" \
  "$ROOT"
