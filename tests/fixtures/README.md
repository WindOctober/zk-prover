Synthetic fixtures under this directory are local test inputs for `zk-prover`.

They are not vendored SV-COMP benchmarks and should not be placed under
`benchmarks/svcomp-initial/vendor/...`.

Current layout:

- `synthetic-c/validation-crafted`: small hand-authored or template-expanded C cases used for
  parser/encoder/UNSAT pipeline testing
