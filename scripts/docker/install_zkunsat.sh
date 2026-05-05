#!/usr/bin/env bash
set -euo pipefail

workspace="${WORKSPACE:-/workspace}"
zkunsat_root="${ZKUNSAT_ROOT:-$workspace/ZKUNSAT}"
local_prefix="${LOCAL_PREFIX:-$zkunsat_root/.local}"
jobs="${JOBS:-$(nproc)}"

: "${ZKUNSAT_REPO:=https://github.com/PP-FM/ZKUNSAT.git}"
: "${ZKUNSAT_REV:=9970d3d3f838425e04d0266b0ce84a55202d9c5b}"
: "${EMP_TOOL_REV:=11093a7d2160e7e7a4dcae3ffd9e6935bf2b8c1c}"
: "${EMP_OT_REV:=52b32c8371c09c1567e3d650c0f0adfbb229a270}"
: "${EMP_ZK_REV:=73ab193a923d4c122be5a4f6bc1fe4f617966b02}"

clone_at_rev() {
  local repo="$1"
  local rev="$2"
  local dest="$3"
  git clone "$repo" "$dest"
  git -C "$dest" checkout "$rev"
}

cmake_install() {
  local src="$1"
  local build="$2"
  cmake -S "$src" -B "$build" \
    -DCMAKE_INSTALL_PREFIX="$local_prefix" \
    -DCMAKE_PREFIX_PATH="$local_prefix"
  cmake --build "$build" -j"$jobs"
  cmake --install "$build"
}

rm -rf "$zkunsat_root"
mkdir -p "$workspace"
clone_at_rev "$ZKUNSAT_REPO" "$ZKUNSAT_REV" "$zkunsat_root"
git -C "$zkunsat_root" apply /tmp/zkunsat-local.patch

mkdir -p "$zkunsat_root/deps" "$zkunsat_root/data"
clone_at_rev https://github.com/emp-toolkit/emp-tool.git "$EMP_TOOL_REV" "$zkunsat_root/deps/emp-tool"
clone_at_rev https://github.com/emp-toolkit/emp-ot.git "$EMP_OT_REV" "$zkunsat_root/deps/emp-ot"
clone_at_rev https://github.com/emp-toolkit/emp-zk.git "$EMP_ZK_REV" "$zkunsat_root/deps/emp-zk"

cmake_install "$zkunsat_root/deps/emp-tool" "$zkunsat_root/deps/build/emp-tool"
cmake_install "$zkunsat_root/deps/emp-ot" "$zkunsat_root/deps/build/emp-ot"
cmake_install "$zkunsat_root/deps/emp-zk" "$zkunsat_root/deps/build/emp-zk"

(
  cd "$zkunsat_root"
  export LOCAL_PREFIX="$local_prefix"
  export CMAKE_PREFIX_PATH="$local_prefix"
  export CPATH="$local_prefix/include:/usr/include/x86_64-linux-gnu${CPATH:+:$CPATH}"
  export LIBRARY_PATH="$local_prefix/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
  export LD_LIBRARY_PATH="$local_prefix/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
  cmake -S . -B build
  cmake --build build -j"$jobs"
)
