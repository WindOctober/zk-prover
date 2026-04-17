# Initial SV-COMP Benchmarks

This directory records the current small benchmark slice for the paper-faithful `Program -> SSA -> VC -> SAT` track.

The selected benchmark files are vendored locally under:

- `vendor/sv-benchmarks`

Local synthetic fixtures used for parser/encoder experiments live under:

- `tests/fixtures`

They are intentionally kept out of this benchmark bundle so the `benchmarks/` tree stays
reserved for vendored or externally sourced benchmark sets.

## Selection Principles

- branch-first, loop-free tasks
- scalar integer / character types only
- no pointers or heap
- no structs/unions
- no helper-function calls in user code
- small files that fit the current `zk-prover` frontend subset

## Source

- Repository: `https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks.git`
- Commit: `ca46fe670b5dcbcd3495bd23689353a8ea1fb86b`

## Why This Slice

The current artifact-validation path is intentionally narrow.
Right now the best-fit SV-COMP tasks are the ones that stay close to:

- single-function control flow
- small scalar bit-vector operations
- direct unreach-call style bad states

Within that subset, a pure loop-free batch exists, but it is small.
So this initial paper-track slice now prefers exact frontend fit over benchmark count.

In practice, the current zero-extension frontend path is narrower than the broader loop-free
SV-COMP subset. Several official scalar bitvector regressions are still vendored locally, but
they are not part of the selected benchmark slice because the current frontend collapses them
into trivial CNFs that are not useful for benchmarking.

## Normalization Note

Some vendored SV-COMP tasks use the canonical pattern:

- `goto ERROR;`
- `ERROR: { reach_error(); abort(); }`

The files are vendored unchanged.
At load time, `zk-prover` applies a narrow source normalization that rewrites only this idiom into a direct `reach_error();` call before parsing.

This keeps the local bundle faithful to SV-COMP while avoiding a broader `goto` frontend effort at this stage.

## Current Set

The current selected set contains two official SV-COMP tasks:

1. `c/validation-crafted/if.c`
2. `c/validation-crafted/ternary.c`

These two are the current benchmark baseline because they both:

- parse and lower without extending the frontend
- encode to non-trivial CNFs
- stay inside the intended no-loop, no-pointer, single-function slice

The currently excluded vendored bitvector regressions under `c/bitvector-regression` remain
useful as parser/lowering regression inputs, but they are not counted as benchmark fixtures for
this slice because they currently encode to degenerate CNFs such as `1 var / 2 clauses`.
