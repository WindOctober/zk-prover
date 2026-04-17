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

- `scripts/run_svcomp_bench.sh`
  - Runs the official SV-COMP slice through the end-to-end `C -> CNF -> SAT` pipeline.
  - Uses `examples/bench_unsat_pipeline.rs` with `--preset svcomp`, so UNSAT proving is only attempted if a selected fixture is actually UNSAT.
- `scripts/run_unsat_bench.sh`
  - Runs the synthetic UNSAT-heavy slice for resolution-proof and backend benchmarking.
  - Uses `examples/bench_unsat_pipeline.rs` with `--preset synthetic-unsat`.
- `examples/bench_resolution_zkvms.rs`
  - Compares HyperPlonk, SP1, Jolt, and zkWASM on prevalidated UNSAT witnesses from the synthetic fixture set.
