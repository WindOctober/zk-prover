# Docker Reproduction

This image localizes the paper experiment stack under `/workspace`:

- `/workspace/zk-prover`: this repository.
- `/workspace/ZKUNSAT`: a cloned ZKUNSAT checkout at the pinned revision used by the benchmark flow.
- `/workspace/ZKUNSAT/.local`: pinned EMP toolkit builds used by ZKUNSAT.

Build:

```bash
scripts/docker/build_image.sh
```

Run a lightweight sanity check:

```bash
docker run --rm \
  -v "$PWD/artifacts:/workspace/zk-prover/artifacts" \
  zk-prover-paper:latest zkunsat-smoke
```

Use `smoke` instead of `zkunsat-smoke` to also run `cargo check --workspace --all-targets --features proof-backends`.

Check the Rocq proof artifact:

```bash
docker run --rm zk-prover-paper:latest proof
```

The image installs `rocq-prover.9.0.0` through opam and checks
`proofs/rocq/theories/ZkProver/SatUnsat.v` with `rocq c`.

Run the RQ2 runner on the smallest checked-in ZKUNSAT proof:

```bash
docker run --rm \
  -v "$PWD/artifacts:/workspace/zk-prover/artifacts" \
  zk-prover-paper:latest rq2-smoke
```

Reproduce RQ1 / Table 2:

```bash
docker run --rm \
  -v "$PWD/artifacts:/workspace/zk-prover/artifacts" \
  -e RUNS=1 -e THREADS=32 \
  zk-prover-paper:latest rq1
```

For a faster pipeline check without SP1 proof generation:

```bash
docker run --rm \
  -v "$PWD/artifacts:/workspace/zk-prover/artifacts" \
  zk-prover-paper:latest rq1-smoke
```

Reproduce RQ2 / Table 3:

```bash
docker run --rm \
  -v "$PWD/artifacts:/workspace/zk-prover/artifacts" \
  -e RUNS=1 -e THREADS=8 \
  zk-prover-paper:latest rq2
```

The full RQ1 SP1 proof run is memory intensive; the paper reports a 64 GiB workstation and records one OOM row. The Docker flow preserves the same behavior through the existing `scripts/run_rq1_bench.sh` failure logging.

`rq2` prepares the combined manifest by default. To use a custom manifest, pass `-e MANIFEST=/path/in/container/manifest.csv`; the entrypoint will skip manifest preparation and run that manifest directly.
