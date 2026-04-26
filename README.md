# zk-prover

A Rust framework for constructing verification-layer artifacts and CNF artifacts from C programs, with SP1-based zkVM validation for the frontend-to-SAT translation path.

## Current Scope

The active direction follows this Phase I design:

`C source -> verification-layer program artifact -> CNF artifact`

In this pipeline, the SP1 zkVM frontend checker validates the correspondence between the verification-layer artifact and the CNF artifact inside the zkVM.

Current implementation status:

- native frontend runner:
  - parse and normalize C input
  - lower C into a serializable verification-layer program artifact
  - build a finite CNF artifact from that verification-layer program with automatically inferred steps for acyclic programs
- zkVM frontend checker:
  - validate `verification program <-> CNF` consistency
  - commit a compact CNF summary/hash

## Layout

- `src/frontend`
  - Frontend normalization, fixture selection, and verification-layer IR construction.
- `src/frontend/runtime`
  - Frontend runtime wrappers for native execution and zkVM validation.
- `src/backend`
  - Backend CNF data structures and the verification-layer to SAT encoder.
- `crates/zkpv-*`
  - Vendored frontend crates for the current C parser/lowering path, kept in-tree so `zk-prover` builds without a sibling `ztor` checkout.
- `benchmarks/svcomp-initial`
  - Local SV-COMP subset used for smoke tests and proof runs.

## Benchmarks

- `scripts/run_rq1_bench.sh`
  - One-command reproduction for the paper RQ1 table.
  - Runs Phase I SP1 proving/verification and Phase II Plonky3 proving/verification on the ten paper fixtures.
  - SAT cases use the Plonky3 SAT backend. UNSAT cases use the committed Plonky3 UNSAT backend with private-formula commitment constraints enabled.
  - Default output root is `artifacts/rq1-<timestamp>`.
  - Main outputs are `results/rq1_summary.csv` and `results/rq1_table.tex`.
- `scripts/run_svcomp_bench.sh`
  - Runs the official SV-COMP slice through the end-to-end `C -> CNF -> SAT` pipeline.
  - Uses `examples/bench_unsat_pipeline.rs` with `--preset svcomp`, so UNSAT proving is only attempted if a selected fixture is actually UNSAT.
- `scripts/run_unsat_bench.sh`
  - Runs the synthetic UNSAT-heavy slice for resolution-proof and backend benchmarking.
  - Uses `examples/bench_unsat_pipeline.rs` with `--preset synthetic-unsat`.
- `examples/bench_resolution_zkvms.rs`
  - Compares HyperPlonk, SP1, Jolt, and zkWASM on prevalidated UNSAT witnesses from the synthetic fixture set.

### RQ1 Reproduction

Run the full RQ1 experiment from the repository root:

```bash
RUNS=1 THREADS=32 ./scripts/run_rq1_bench.sh
```

The script builds PicoSAT with trace support if `PICOSAT_BIN` does not point to an existing binary. It then writes raw Phase I/Phase II CSVs plus the final table files under `OUT_DIR`:

```bash
OUT_DIR=artifacts/rq1-paper RUNS=1 THREADS=32 ./scripts/run_rq1_bench.sh
```

Useful knobs:

- `RUNS`: repetitions per fixture/backend; the formatter reports medians.
- `THREADS`: `RAYON_NUM_THREADS` for Plonky3 Phase II proving.
- `OUT_DIR`: destination artifact directory.
- `PICOSAT_BIN`: existing PicoSAT binary compiled with trace support.
- `P1_PROOF_ONLY`: skip the Phase I `execute()` pass and record only proving/verification/proof-size costs; default is `1` because RQ1 does not report exec time.
- `P1_SHARD_SIZE`: optional SP1 core shard-size override for Phase I proving; unset by default, so SP1 uses its own default shard size.
- `P1_SKIP_PROVE=1`: smoke-test mode for checking the pipeline without SP1 proof generation.
- `CONTINUE_ON_P1_ERROR`: keep running Phase II if a local SP1 proof is killed or fails; default is `1`, with failed fixtures listed in `phase1_*.csv.failures`.
- `RUN_PHASE1` / `RUN_PHASE2`: set either one to `0` to rerun only the other phase before reformatting existing artifacts.

The generated `results/rq1_table.tex` uses the compact cell format `prove(s) / verify(ms) / proof(KiB)`.
