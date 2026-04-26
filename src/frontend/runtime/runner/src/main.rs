use std::{fs, path::PathBuf, time::Instant};

use clap::Parser;
use sp1_sdk::blocking::{ProveRequest, Prover, ProverClient, SP1Stdin};
use sp1_sdk::include_elf;
use sp1_sdk::utils::setup_logger;
use sp1_sdk::{Elf, ProvingKey};
use zk_prover::{encode_c_source_to_cnf, CnfSummary, DEFAULT_FIXTURES};

const ELF: Elf = include_elf!("zk-prover-frontend-zkvm");

#[derive(Debug, Parser)]
struct Args {
    #[arg(long = "fixture")]
    fixtures: Vec<String>,
    #[arg(long)]
    benchmark_root: Option<PathBuf>,
    #[arg(long)]
    skip_prove: bool,
    #[arg(long)]
    proof_only: bool,
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
    let benchmark_root = args.benchmark_root.unwrap_or_else(|| {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../../benchmarks/svcomp-initial")
    });

    let prover = ProverClient::builder().cpu().build();
    let pk = prover.setup(ELF).expect("failed to setup SP1 proving key");

    println!(
        "fixture,run,exec_ms,prove_ms,verify_ms,proof_bytes,instructions,gas,validate_cycles,steps,blocks,program_vars,nondet_symbols,cnf_vars,cnf_clauses,commit_num_vars,commit_num_clauses,commit_width,commit_mix_a,commit_mix_b,cnf_digest"
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
                args.proof_only,
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
    proof_only: bool,
) -> String {
    let local_encoded = encode_c_source_to_cnf(source).expect("failed to encode C source to CNF");
    let local_summary = CnfSummary::from_encoded(&local_encoded);
    let stdin = build_stdin(source);

    let mut execute_ms = 0.0;
    let mut instructions = 0u64;
    let mut gas = 0u64;
    let mut validate_cycles = 0u64;
    let mut expected_summary = local_summary.clone();

    if !proof_only {
        let execute_started = Instant::now();
        let (mut public_values, report) = prover
            .execute(ELF, stdin.clone())
            .calculate_gas(true)
            .run()
            .expect("execution failed");
        execute_ms = execute_started.elapsed().as_secs_f64() * 1000.0;
        let execute_summary = public_values.read::<CnfSummary>();

        assert_eq!(
            local_summary, execute_summary,
            "local/SP1 encoding diverged for fixture `{fixture}`"
        );

        instructions = report.total_instruction_count();
        gas = report.gas().unwrap_or(0);
        validate_cycles = report.cycle_tracker.get("validate").copied().unwrap_or(0);
        expected_summary = execute_summary;
    }

    let mut prove_ms = 0.0;
    let mut verify_ms = 0.0;
    let mut proof_bytes = 0u64;

    if !skip_prove {
        let prove_started = Instant::now();
        let mut proof = prover
            .prove(pk, stdin)
            .core()
            .run()
            .expect("proof generation failed");
        prove_ms = prove_started.elapsed().as_secs_f64() * 1000.0;
        proof_bytes = bincode::serialized_size(&proof).expect("failed to measure proof size");

        let verify_started = Instant::now();
        prover
            .verify(&proof, pk.verifying_key(), None)
            .expect("proof verification failed");
        verify_ms = verify_started.elapsed().as_secs_f64() * 1000.0;

        let proof_summary = proof.public_values.read::<CnfSummary>();
        assert_eq!(
            expected_summary, proof_summary,
            "expected/prove public values diverged for fixture `{fixture}`"
        );
    }

    format!(
        "{fixture},{run_index},{execute_ms:.3},{prove_ms:.3},{verify_ms:.3},{proof_bytes},{instructions},{gas},{validate_cycles},{steps},{blocks},{program_vars},{nondet_symbols},{cnf_vars},{cnf_clauses},{commit_num_vars},{commit_num_clauses},{commit_width},{commit_mix_a},{commit_mix_b},{cnf_digest}",
        proof_bytes = proof_bytes,
        instructions = instructions,
        gas = gas,
        validate_cycles = validate_cycles,
        steps = expected_summary.steps,
        blocks = expected_summary.blocks,
        program_vars = expected_summary.program_vars,
        nondet_symbols = expected_summary.nondet_symbols,
        cnf_vars = expected_summary.cnf_vars,
        cnf_clauses = expected_summary.cnf_clauses,
        commit_num_vars = expected_summary.cnf_commitment.num_vars,
        commit_num_clauses = expected_summary.cnf_commitment.num_clauses,
        commit_width = expected_summary.cnf_commitment.max_clause_width,
        commit_mix_a = expected_summary.cnf_commitment.mix_a,
        commit_mix_b = expected_summary.cnf_commitment.mix_b,
        cnf_digest = hex_digest(&expected_summary.cnf_digest),
    )
}

fn build_stdin(source: &str) -> SP1Stdin {
    let mut stdin = SP1Stdin::new();
    stdin.write(&source.to_owned());
    stdin
}

fn hex_digest(bytes: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}
