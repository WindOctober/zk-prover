# Initial SV-COMP Benchmarks

This directory records the current small benchmark slice for the paper-faithful `Program -> SSA -> VC -> SAT` track.

The selected benchmark files are vendored locally under:

- `vendor/sv-benchmarks`

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

## Normalization Note

Some vendored SV-COMP tasks use the canonical pattern:

- `goto ERROR;`
- `ERROR: { reach_error(); abort(); }`

The files are vendored unchanged.
At load time, `zk-prover` applies a narrow source normalization that rewrites only this idiom into a direct `reach_error();` call before parsing.

This keeps the local bundle faithful to SV-COMP while avoiding a broader `goto` frontend effort at this stage.

## Current Set

The current set contains ten loop-free tasks:

1. `c/validation-crafted/if.c`
2. `c/validation-crafted/ternary.c`
3. `c/bitvector-regression/implicitunsignedconversion-1.c`
4. `c/bitvector-regression/implicitunsignedconversion-2.c`
5. `c/bitvector-regression/integerpromotion-2.c`
6. `c/bitvector-regression/integerpromotion-3.c`
7. `c/bitvector-regression/signextension-1.c`
8. `c/bitvector-regression/signextension-2.c`
9. `c/bitvector-regression/signextension2-1.c`
10. `c/bitvector-regression/signextension2-2.c`
