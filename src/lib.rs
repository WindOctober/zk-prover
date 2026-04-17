pub mod backend;
pub mod frontend;

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

pub use backend::cnf::CnfFormula;
pub use frontend::fixtures::{
    DEFAULT_FIXTURES, RESOLUTION_ZKVM_FIXTURES, SAT_PHASE_FIXTURES, SVCOMP_BENCHMARK_ROOT,
    SVCOMP_FIXTURES, SYNTHETIC_FIXTURES, SYNTHETIC_FIXTURE_ROOT, UNSAT_PIPELINE_FIXTURES,
};
pub use frontend::ir::VerificationProgram;
use frontend::normalize::normalize_svcomp_source;
pub use resolution_verifier_core::{
    decode_witness_words, encode_witness_words, verify_flat_resolution_witness,
    verify_witness_words, FlatResolutionWitness, ResolutionVerificationError,
    ResolutionVerificationSummary,
};
use zkpv_c0_lowering::{lower_translation_unit, LoweringError};
use zkpv_c0_parser::{parse_translation_unit, ParseError};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncodedCnf {
    pub steps: u32,
    pub blocks: u32,
    pub program_vars: u32,
    pub nondet_symbols: u32,
    pub cnf: CnfFormula,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TranslationArtifact {
    pub program: VerificationProgram,
    pub steps: u32,
    pub cnf: CnfFormula,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CnfSummary {
    pub steps: u32,
    pub blocks: u32,
    pub program_vars: u32,
    pub nondet_symbols: u32,
    pub cnf_vars: u32,
    pub cnf_clauses: u32,
    pub cnf_digest: [u8; 32],
}

impl CnfSummary {
    pub fn from_encoded(encoded: &EncodedCnf) -> Self {
        Self {
            steps: encoded.steps,
            blocks: encoded.blocks,
            program_vars: encoded.program_vars,
            nondet_symbols: encoded.nondet_symbols,
            cnf_vars: encoded.cnf.num_vars,
            cnf_clauses: encoded.cnf.clauses.len() as u32,
            cnf_digest: encoded.cnf.sha256_digest(),
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum EncodeError {
    #[error("parse error: {0}")]
    Parse(#[from] ParseError),
    #[error("lowering error: {0}")]
    Lower(#[from] LoweringError),
    #[error("verification-layer conversion error: {0}")]
    VerificationProgram(String),
    #[error("unsupported construct for CNF encoding: {0}")]
    Unsupported(String),
    #[error("artifact validation failed: {0}")]
    ArtifactMismatch(String),
}

pub fn lower_c_source_to_program(source: &str) -> Result<VerificationProgram, EncodeError> {
    let normalized = normalize_svcomp_source(source);
    let unit = parse_translation_unit(&normalized)?;
    let lowered = lower_translation_unit(&unit)?;
    VerificationProgram::try_from(lowered).map_err(EncodeError::VerificationProgram)
}

pub fn encode_c_source_to_cnf(source: &str) -> Result<EncodedCnf, EncodeError> {
    let program = lower_c_source_to_program(source)?;
    encode_program_to_cnf(&program)
}

pub fn encode_program_to_cnf(program: &VerificationProgram) -> Result<EncodedCnf, EncodeError> {
    let steps = infer_encoding_steps(program)?;
    backend::encoder::encode_program_to_cnf(program, steps)
}

pub fn build_translation_artifact_from_c_source(
    source: &str,
) -> Result<TranslationArtifact, EncodeError> {
    let program = lower_c_source_to_program(source)?;
    build_translation_artifact_from_program(program)
}

pub fn build_translation_artifact_from_program(
    program: VerificationProgram,
) -> Result<TranslationArtifact, EncodeError> {
    let encoded = encode_program_to_cnf(&program)?;
    Ok(TranslationArtifact {
        program,
        steps: encoded.steps,
        cnf: encoded.cnf,
    })
}

pub fn validate_translation_artifact(
    artifact: &TranslationArtifact,
) -> Result<CnfSummary, EncodeError> {
    let encoded = encode_program_to_cnf(&artifact.program)?;
    if encoded.steps != artifact.steps {
        return Err(EncodeError::ArtifactMismatch(
            "re-encoded step count does not match supplied artifact".to_owned(),
        ));
    }
    if encoded.cnf != artifact.cnf {
        return Err(EncodeError::ArtifactMismatch(
            "re-encoded CNF does not match supplied artifact".to_owned(),
        ));
    }
    Ok(CnfSummary::from_encoded(&encoded))
}

fn infer_encoding_steps(program: &VerificationProgram) -> Result<u32, EncodeError> {
    if has_cycle(program) {
        return Err(EncodeError::Unsupported(
            "cyclic control-flow requires an explicit loop/recursion handling strategy".to_owned(),
        ));
    }

    Ok((program.blocks.len().saturating_sub(1) as u32).max(1))
}

fn has_cycle(program: &VerificationProgram) -> bool {
    let blocks = program
        .blocks
        .iter()
        .map(|block| (block.id, block))
        .collect::<BTreeMap<_, _>>();
    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();

    fn dfs(
        block_id: u32,
        exit_block: u32,
        error_block: u32,
        blocks: &BTreeMap<u32, &frontend::ir::BasicBlock>,
        visiting: &mut BTreeSet<u32>,
        visited: &mut BTreeSet<u32>,
    ) -> bool {
        if block_id == exit_block || block_id == error_block {
            return false;
        }
        let Some(block) = blocks.get(&block_id) else {
            return false;
        };
        if visiting.contains(&block_id) {
            return true;
        }
        if visited.contains(&block_id) {
            return false;
        }

        visiting.insert(block_id);

        match &block.terminator {
            frontend::ir::Terminator::Goto(target) => {
                if dfs(*target, exit_block, error_block, blocks, visiting, visited) {
                    return true;
                }
            }
            frontend::ir::Terminator::Branch {
                then_block,
                else_block,
                ..
            } => {
                if dfs(
                    *then_block,
                    exit_block,
                    error_block,
                    blocks,
                    visiting,
                    visited,
                ) || dfs(
                    *else_block,
                    exit_block,
                    error_block,
                    blocks,
                    visiting,
                    visited,
                ) {
                    return true;
                }
            }
            frontend::ir::Terminator::Return => {}
        }

        visiting.remove(&block_id);
        visited.insert(block_id);
        false
    }

    dfs(
        program.entry_block,
        program.exit_block,
        program.error_block,
        &blocks,
        &mut visiting,
        &mut visited,
    )
}

#[cfg(test)]
mod tests {
    use std::{fs, path::PathBuf, time::Instant};

    use super::*;

    #[test]
    fn encodes_small_bug_and_safe_examples() {
        let safe = r#"
            int main() {
                int x = 0;
                __VERIFIER_assert(x == 0);
                return 0;
            }
        "#;
        let bug = r#"
            int main() {
                int x = 0;
                __VERIFIER_assert(x == 1);
                return 0;
            }
        "#;

        let safe_encoded = encode_c_source_to_cnf(safe).unwrap();
        let bug_encoded = encode_c_source_to_cnf(bug).unwrap();

        assert!(safe_encoded.cnf.num_vars > 0);
        assert!(bug_encoded.cnf.num_vars > 0);
        assert!(bug_encoded.cnf.clauses.len() >= safe_encoded.cnf.clauses.len());
    }

    #[test]
    fn encodes_all_current_benchmarks() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(SVCOMP_BENCHMARK_ROOT);

        for fixture in SVCOMP_FIXTURES {
            let source = fs::read_to_string(root.join(fixture)).unwrap();
            let artifact = build_translation_artifact_from_c_source(&source)
                .unwrap_or_else(|err| panic!("failed to build artifact for {fixture}: {err}"));
            let summary = validate_translation_artifact(&artifact)
                .unwrap_or_else(|err| panic!("failed to validate artifact for {fixture}: {err}"));
            assert!(
                summary.cnf_vars > 0 && summary.cnf_clauses > 0,
                "empty CNF for {fixture}"
            );
        }
    }

    #[test]
    fn encodes_all_current_synthetic_fixtures() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(SYNTHETIC_FIXTURE_ROOT);

        for fixture in SYNTHETIC_FIXTURES {
            let source = fs::read_to_string(root.join(fixture)).unwrap();
            let artifact = build_translation_artifact_from_c_source(&source)
                .unwrap_or_else(|err| panic!("failed to build artifact for {fixture}: {err}"));
            let summary = validate_translation_artifact(&artifact)
                .unwrap_or_else(|err| panic!("failed to validate artifact for {fixture}: {err}"));
            assert!(
                summary.cnf_vars > 0 && summary.cnf_clauses > 0,
                "empty CNF for {fixture}"
            );
        }
    }

    #[test]
    fn keeps_if_fixture_cnf_compact() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(SVCOMP_BENCHMARK_ROOT);
        let fixture = "vendor/sv-benchmarks/c/validation-crafted/if.c";
        let source = fs::read_to_string(root.join(fixture)).unwrap();
        let started = Instant::now();
        let encoded = encode_c_source_to_cnf(&source).unwrap();
        let encode_ms = started.elapsed().as_secs_f64() * 1000.0;

        eprintln!(
            "if.c summary: encode_ms={encode_ms:.3} nondet_symbols={} cnf_vars={} cnf_clauses={}",
            encoded.nondet_symbols,
            encoded.cnf.num_vars,
            encoded.cnf.clauses.len()
        );

        assert_eq!(encoded.nondet_symbols, 2);
        assert!(encoded.cnf.num_vars < 5_000);
        assert!(encoded.cnf.clauses.len() < 20_000);
    }

    #[test]
    fn rejects_cyclic_control_flow_without_bound_interface() {
        let looping = r#"
            int main() {
                int x = 0;
                while (x == 0) {
                    x = 0;
                }
                return 0;
            }
        "#;

        let err = build_translation_artifact_from_c_source(looping).unwrap_err();
        assert!(matches!(err, EncodeError::Unsupported(_)));
    }
}
