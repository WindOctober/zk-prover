# ZKUNSAT Exp2 Benchmarks

This benchmark set compares the Plonky3 UNSAT backend against the ZKUNSAT interactive verifier on unfolded resolution proofs. The combined Exp2 set uses SV-COMP-derived proofs generated locally and selected unfolded proofs distributed in the local ZKUNSAT stable artifact.

The manifest records the selected instances and their expected proof statistics. Some rows correspond to historical ZKUNSAT result logs whose unfolded proof files are not present in the current checkout. The runner reports those rows as `missing` rather than fabricating measurements.

Run from the repository root:

```bash
OUT_DIR=$PWD/artifacts/zkunsat-exp2-combined scripts/prepare_zkunsat_exp2_combined.sh

RUN_ZKUNSAT_BUILD=0 \
MANIFEST=$PWD/artifacts/zkunsat-exp2-combined/manifest.csv \
OUT_DIR=artifacts/zkunsat-exp2-combined-run \
THREADS=8 RUNS=1 \
scripts/run_zkunsat_exp2.sh
```

Useful overrides:

```bash
RUNS=3 THREADS=8 scripts/run_zkunsat_exp2.sh
RUN_ZKUNSAT_BUILD=0 scripts/run_zkunsat_exp2.sh --fixture zkunsat_example_small
scripts/run_zkunsat_exp2.sh --skip-zkunsat
```

If a machine cannot run the full set in one process, run selected fixtures with
`--fixture <slug>` and then collect the existing per-fixture `result.json` files:

```bash
python3 scripts/collect_zkunsat_exp2_results.py \
  --manifest artifacts/zkunsat-exp2-combined/manifest.csv \
  --output-dir artifacts/zkunsat-exp2-combined-run
```

Outputs are written to `artifacts/zkunsat-exp2/` by default:

- `results/summary.csv`: machine-readable combined results.
- `results/summary.md`: pretty table for quick inspection.
- `fixtures/<slug>/`: per-instance logs, decompressed unfolded proofs when needed, and backend artifacts.
