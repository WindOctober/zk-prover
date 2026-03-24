use std::{fs, path::PathBuf, time::Instant};

use clap::Parser;
use sp1_sdk::blocking::{ProveRequest, Prover, ProverClient, SP1Stdin};
use sp1_sdk::include_elf;
use sp1_sdk::utils::setup_logger;
use sp1_sdk::{Elf, ProvingKey};
use zk_prover::{
    build_translation_artifact_from_c_source, validate_translation_artifact, CnfSummary,
    TranslationArtifact, DEFAULT_FIXTURES,
};

const ELF: Elf = include_elf!("zk-prover-frontend-zkvm");

#[derive(Debug, Parser)]
struct Args {
    #[arg(long = "fixture")]
    fixtures: Vec<String>,
    #[arg(long)]
    skip_prove: bool,
    #[arg(long, default_value_t = 1)]
    repeat: u32,
}

fn main() {
    let args = Args::parse();
    setup_logger();

    let fixtures = if args.fixtures.is_empty() {
        DEFAULT_FIXTURES
            .iter()
            .map(|fixture| fixture.to_string())
            .collect::<Vec<_>>()
    } else {
        args.fixtures.clone()
    };
    let benchmark_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../../../benchmarks/svcomp-initial");

    let prover = ProverClient::builder().cpu().build();
    let pk = prover.setup(ELF).expect("failed to setup SP1 proving key");

    println!(
        "fixture,run,exec_ms,prove_ms,verify_ms,instructions,gas,validate_cycles,steps,blocks,program_vars,nondet_symbols,cnf_vars,cnf_clauses,cnf_hash"
    );

    for fixture in fixtures {
        let source = fs::read_to_string(benchmark_root.join(&fixture))
            .unwrap_or_else(|err| panic!("failed to read fixture `{fixture}`: {err}"));

        for run_index in 0..args.repeat {
            let summary = run_one(
                &prover,
                &pk,
                &fixture,
                &source,
                run_index,
                args.skip_prove,
            );
            println!("{summary}");
        }
    }
}

fn run_one<P: Prover>(
    prover: &P,
    pk: &P::ProvingKey,
    fixture: &str,
    source: &str,
    run_index: u32,
    skip_prove: bool,
) -> String {
    let artifact =
        build_translation_artifact_from_c_source(source).expect("failed to build SAT artifact");
    let local_summary =
        validate_translation_artifact(&artifact).expect("local SAT artifact validation failed");
    let stdin = build_stdin(&artifact);

    let execute_started = Instant::now();
    let (mut public_values, report) = prover
        .execute(ELF, stdin.clone())
        .calculate_gas(true)
        .run()
        .expect("execution failed");
    let execute_ms = execute_started.elapsed().as_secs_f64() * 1000.0;
    let execute_summary = public_values.read::<CnfSummary>();

    assert_eq!(
        local_summary, execute_summary,
        "local/SP1 encoding diverged for fixture `{fixture}`"
    );

    let mut prove_ms = 0.0;
    let mut verify_ms = 0.0;

    if !skip_prove {
        let prove_started = Instant::now();
        let mut proof = prover
            .prove(pk, stdin)
            .core()
            .run()
            .expect("proof generation failed");
        prove_ms = prove_started.elapsed().as_secs_f64() * 1000.0;

        let verify_started = Instant::now();
        prover
            .verify(&proof, pk.verifying_key(), None)
            .expect("proof verification failed");
        verify_ms = verify_started.elapsed().as_secs_f64() * 1000.0;

        let proof_summary = proof.public_values.read::<CnfSummary>();
        assert_eq!(
            execute_summary, proof_summary,
            "execute/prove public values diverged for fixture `{fixture}`"
        );
    }

    format!(
        "{fixture},{run_index},{execute_ms:.3},{prove_ms:.3},{verify_ms:.3},{instructions},{gas},{validate_cycles},{steps},{blocks},{program_vars},{nondet_symbols},{cnf_vars},{cnf_clauses},{cnf_hash}",
        instructions = report.total_instruction_count(),
        gas = report.gas().unwrap_or(0),
        validate_cycles = report.cycle_tracker.get("validate").copied().unwrap_or(0),
        steps = execute_summary.steps,
        blocks = execute_summary.blocks,
        program_vars = execute_summary.program_vars,
        nondet_symbols = execute_summary.nondet_symbols,
        cnf_vars = execute_summary.cnf_vars,
        cnf_clauses = execute_summary.cnf_clauses,
        cnf_hash = execute_summary.cnf_hash,
    )
}

fn build_stdin(artifact: &TranslationArtifact) -> SP1Stdin {
    let mut stdin = SP1Stdin::new();
    stdin.write(artifact);
    stdin
}
