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
- `benchmarks/svcomp-initial`
  - Local SV-COMP subset used for smoke tests and proof runs.
