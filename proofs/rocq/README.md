# Rocq Proof Artifacts

This directory contains a small Rocq development for the circuit-level
soundness layer of ZK-ProVer's Phase II logic.

The formalization stops at the matrix/constraint boundary.  It does not model
the polynomial commitments, STARK backend, or any concrete field arithmetic.
Instead it proves that:

- SAT circuit constraints imply that the private witness assignment satisfies
  the CNF formula.
- UNSAT circuit constraints imply that the private witness is a valid
  resolution refutation.
- A valid resolution refutation rules out every satisfying assignment.

The UNSAT side models the source verifier's one-based `clause_by_id` parent
lookup and the Plonky3 AIR's oriented resolution trace.  The Rocq development
defines the source-aligned matrix layout constants such as
`RES_IS_DERIVED_COL`, `RES_LEFT_ID_COL`, `RES_HEADER_WIDTH`, and the dynamic
literal/keep-flag column bases.  `trace_row_extracts_air` lowers a concrete
trace row at those matrix columns into a `ResolutionAirRow`.
`resolution_trace_row_constraints` also constrains the auxiliary column blocks
used by the AIR executor: zero witnesses, pivot equality flags, parent gap
limbs, inverse/header columns, source/selected prefix counts, and fingerprint
product accumulators. The resolution membership facts are not assumed directly:
pivot membership is derived from pivot-count constraints, source/selected
membership is derived from the AIR-style source/selected count and fingerprint
accumulator final equalities, and current clause membership is derived from
the AIR keep gate forcing each nonzero current literal to be selected by a
left or right keep flag.
`resolution_trace_matrix_steps_valid_with_rows_air_sound` then proves that
these matrix-column constraints imply the previous `resolution_air_steps_valid`
predicate.

Parent lookup is also kept at the matrix/permutation boundary rather than
assumed as a logical `clause_by_id` fact. `resolution_clause_bus_constraints`
models the source AIR's clause bus tuples `(clause_id, literals...)`: a
derived row's current, left-parent, and right-parent clause blocks must match
the corresponding rows of `clause_matrix`. The soundness proof uses
`resolution_matrix_encodes` for the initial formula rows and extends the known
matrix rows with each derived current clause, deriving the logical
`clause_by_id` parent facts from those bus constraints.

This proof intentionally does not formalize finite-field collision bounds for
the fingerprint products or the STARK/permutation argument. Those belong below
the matrix/constraint boundary; here they are represented as explicit
matrix-column consistency predicates.

The row-level resolution semantics match the executor and AIR orientation: the
left parent drops only the positive pivot literal, and the right parent drops
only the negative pivot literal. The keep/source membership facts are proved
from slot predicates over the current, left, and right clause blocks read from
the matrix columns, not injected as direct row-level premises.

The proof uses no `Axiom` and no `Admitted`.

## Local Build

With Rocq installed:

```bash
make -C proofs/rocq COQC="rocq c"
```

With a compatibility Coq installation:

```bash
make -C proofs/rocq
```

The pinned opam package for reproducible Rocq builds is
`rocq-prover.9.0.0`, which is the current latest package in this environment.
