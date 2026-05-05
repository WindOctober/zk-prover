# syntax=docker/dockerfile:1.7
FROM ubuntu:22.04

ARG DEBIAN_FRONTEND=noninteractive
ARG RUST_TOOLCHAIN=1.94.1
ARG SP1_VERSION=6.0.2
ARG ROCQ_VERSION=9.0.0
ARG ZKUNSAT_REPO=https://github.com/PP-FM/ZKUNSAT.git
ARG ZKUNSAT_REV=9970d3d3f838425e04d0266b0ce84a55202d9c5b
ARG EMP_TOOL_REV=11093a7d2160e7e7a4dcae3ffd9e6935bf2b8c1c
ARG EMP_OT_REV=52b32c8371c09c1567e3d650c0f0adfbb229a270
ARG EMP_ZK_REV=73ab193a923d4c122be5a4f6bc1fe4f617966b02
ARG PICOSAT_URL=https://fmv.jku.at/picosat/picosat-965.tar.gz

ENV TZ=UTC
ENV WORKSPACE=/workspace
ENV ZK_PROVER_ROOT=/workspace/zk-prover
ENV ZKUNSAT_ROOT=/workspace/ZKUNSAT
ENV ZKUNSAT_BIN=/workspace/ZKUNSAT/build/test
ENV LOCAL_PREFIX=/workspace/ZKUNSAT/.local
ENV CMAKE_PREFIX_PATH=/workspace/ZKUNSAT/.local
ENV CPATH=/workspace/ZKUNSAT/.local/include:/usr/include/x86_64-linux-gnu
ENV LIBRARY_PATH=/workspace/ZKUNSAT/.local/lib
ENV LD_LIBRARY_PATH=/workspace/ZKUNSAT/.local/lib
ENV PKG_CONFIG_PATH=/workspace/ZKUNSAT/.local/lib/pkgconfig
ENV OPAMROOT=/opt/opam
ENV PATH=/opt/opam/rocq/bin:/root/.cargo/bin:/root/.sp1/bin:/workspace/zk-prover/scripts/docker:$PATH

RUN apt-get update \
    && apt-get install -y --no-install-recommends software-properties-common \
    && add-apt-repository -y universe \
    && apt-get update \
    && apt-get install -y --no-install-recommends \
      build-essential \
      ca-certificates \
      clang \
      cmake \
      curl \
      git \
      gzip \
      lld \
      m4 \
      make \
      ocaml \
      opam \
      picosat \
      pkg-config \
      protobuf-compiler \
      python3 \
      python3-pip \
      unzip \
      xz-utils \
      zlib1g-dev \
      libclang-dev \
      libgf2x-dev \
      libgmp-dev \
      libprotobuf-dev \
      libntl-dev \
      libssl-dev \
      cbmc \
    && rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
      | sh -s -- -y --profile minimal --default-toolchain "${RUST_TOOLCHAIN}" \
    && rustup component add rustfmt clippy \
    && curl -L https://sp1up.succinct.xyz | bash \
    && /root/.sp1/bin/sp1up -v "${SP1_VERSION}"

RUN opam init --disable-sandboxing --bare -y \
    && opam switch create rocq ocaml-system -y \
    && opam install --switch=rocq -y "rocq-prover.${ROCQ_VERSION}" \
    && opam clean -a -c -s --logs \
    && opam exec --switch=rocq -- rocq --version

WORKDIR /workspace
COPY docker/zkunsat-local.patch /tmp/zkunsat-local.patch
COPY scripts/docker/install_zkunsat.sh /tmp/install_zkunsat.sh
RUN ZKUNSAT_REPO="${ZKUNSAT_REPO}" \
    ZKUNSAT_REV="${ZKUNSAT_REV}" \
    EMP_TOOL_REV="${EMP_TOOL_REV}" \
    EMP_OT_REV="${EMP_OT_REV}" \
    EMP_ZK_REV="${EMP_ZK_REV}" \
    /tmp/install_zkunsat.sh

RUN mkdir -p /tmp/picosat-965 \
    && curl -fsSL "${PICOSAT_URL}" -o /tmp/picosat-965.tar.gz \
    && tar -xzf /tmp/picosat-965.tar.gz -C /tmp/picosat-965 --strip-components=1 \
    && cd /tmp/picosat-965 \
    && CFLAGS= CC=gcc ./configure.sh -t \
    && make -j"$(nproc)" picosat \
    && install -m 0755 picosat /usr/local/bin/picosat-trace \
    && rm -rf /tmp/picosat-965 /tmp/picosat-965.tar.gz

COPY . /workspace/zk-prover
WORKDIR /workspace/zk-prover
RUN mkdir -p /workspace/zk-prover/.cache/picosat-965 \
    && printf '#!/usr/bin/env bash\nexec /usr/local/bin/picosat-trace "$@"\n' \
      > /workspace/zk-prover/.cache/picosat-965/picosat \
    && chmod +x /workspace/zk-prover/.cache/picosat-965/picosat
RUN cargo fetch --locked

ENTRYPOINT ["/workspace/zk-prover/scripts/docker/reproduce_paper.sh"]
CMD ["help"]
