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
lookup and the Plonky3 AIR's oriented resolution rows: the left parent drops
only the positive pivot literal, and the right parent drops only the negative
pivot literal. The row-level keep/source constraints are represented as
logical multiset membership constraints over the current, left, and right
clause blocks.

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
