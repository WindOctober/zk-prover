pub const SVCOMP_BENCHMARK_ROOT: &str = "benchmarks/svcomp-initial";
pub const SYNTHETIC_FIXTURE_ROOT: &str = "tests/fixtures";

pub const SVCOMP_FIXTURES: &[&str] = &[
    "vendor/sv-benchmarks/c/validation-crafted/if.c",
    "vendor/sv-benchmarks/c/validation-crafted/ternary.c",
];

pub const SAT_PHASE_FIXTURES: &[&str] = SVCOMP_FIXTURES;

pub const SYNTHETIC_FIXTURES: &[&str] = &[
    "synthetic-c/validation-crafted/branch_sum_safe.c",
    "synthetic-c/validation-crafted/range_arith_safe.c",
    "synthetic-c/validation-crafted/diamond_safe.c",
    "synthetic-c/validation-crafted/nested_guard_safe.c",
    "synthetic-c/validation-crafted/branch_sum_bug.c",
    "synthetic-c/validation-crafted/equality_chain_bug.c",
    "synthetic-c/validation-crafted/abs_zero_bug.c",
    "synthetic-c/validation-crafted/nested_guard_bug.c",
    "synthetic-c/validation-crafted/range_pack_2_safe.c",
    "synthetic-c/validation-crafted/range_pack_4_safe.c",
    "synthetic-c/validation-crafted/range_pack_8_safe.c",
];

pub const UNSAT_PIPELINE_FIXTURES: &[&str] = &[
    "synthetic-c/validation-crafted/branch_sum_safe.c",
    "synthetic-c/validation-crafted/range_arith_safe.c",
    "synthetic-c/validation-crafted/diamond_safe.c",
    "synthetic-c/validation-crafted/nested_guard_safe.c",
    "synthetic-c/validation-crafted/range_pack_2_safe.c",
    "synthetic-c/validation-crafted/range_pack_4_safe.c",
    "synthetic-c/validation-crafted/range_pack_8_safe.c",
];

pub const RESOLUTION_ZKVM_FIXTURES: &[&str] = &[
    "synthetic-c/validation-crafted/range_arith_safe.c",
    "synthetic-c/validation-crafted/range_pack_2_safe.c",
    "synthetic-c/validation-crafted/range_pack_4_safe.c",
];

pub const DEFAULT_FIXTURES: &[&str] = SVCOMP_FIXTURES;
