#![cfg(feature = "backend-hyperplonk")]

use std::{
    env,
    error::Error,
    fs, io,
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Stdio},
    time::Instant,
};

use serde::{Deserialize, Serialize};
use zk_prover::{
    backend::{
        halo2::hyperplonk::{
            prove_unsat as prove_hyperplonk_unsat, verify_unsat as verify_hyperplonk_unsat,
        },
        phase2::{validate_resolution_instance_from_unfolded_trace, ValidatedResolutionInstance},
    },
    encode_c_source_to_cnf, encode_witness_words, RESOLUTION_ZKVM_FIXTURES, SYNTHETIC_FIXTURE_ROOT,
};

#[derive(Debug, Clone)]
struct Args {
    benchmark_root: PathBuf,
    output_dir: PathBuf,
    picosat: PathBuf,
    fixtures: Vec<String>,
    runs: usize,
    zkunsat_root: PathBuf,
    sp1_examples_root: PathBuf,
    jolt_root: PathBuf,
    zkwasm_root: PathBuf,
    zkwasm_example_root: PathBuf,
    zkwasm_guest_root: PathBuf,
    zkwasm_k: u32,
    run_hyperplonk: bool,
    run_sp1: bool,
    run_jolt: bool,
    run_zkwasm: bool,
}

#[derive(Debug, Clone, Serialize)]
struct FixtureSummary {
    fixture: String,
    vars: u32,
    clauses: usize,
    resolution_steps: usize,
    max_clause_width: u32,
    hyperplonk: Option<BenchAggregate>,
    sp1: Option<BenchAggregate>,
    jolt: Option<BenchAggregate>,
    zkwasm: Option<BenchAggregate>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SingleRunBench {
    backend: String,
    setup_ms: f64,
    prove_ms: f64,
    verify_ms: f64,
    end_to_end_ms: f64,
    proof_bytes: Option<u64>,
    num_vars: u32,
    initial_clause_count: u32,
    resolution_steps: u32,
    max_clause_width: u32,
}

#[derive(Debug, Clone, Serialize)]
struct BenchAggregate {
    backend: String,
    runs: usize,
    samples: Vec<SingleRunBench>,
    median_end_to_end_ms: f64,
    average_end_to_end_ms: f64,
    median_prove_ms: f64,
    median_verify_ms: f64,
    median_setup_ms: f64,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse()?;
    fs::create_dir_all(args.output_dir.join("fixtures"))?;
    fs::create_dir_all(args.output_dir.join("results"))?;

    if args.run_jolt {
        ensure_jolt_cli(&args.jolt_root)?;
    }
    let mut summaries = Vec::new();

    for fixture in &args.fixtures {
        let prepared = prepare_case(&args, fixture)?;
        let fixture_dir = prepared.fixture_dir.clone();

        let hyperplonk = if args.run_hyperplonk {
            benchmark_backend(args.runs, || run_hyperplonk(&prepared))
                .map_err(|err| {
                    record_backend_failure(&fixture_dir, "hyperplonk", &err.to_string()).ok();
                    err
                })
                .ok()
        } else {
            None
        };

        let sp1 = if args.run_sp1 {
            benchmark_backend(args.runs, || {
                run_external_json_backend(
                    &args.sp1_examples_root,
                    &[
                        "cargo",
                        "run",
                        "-p",
                        "resolution-proof-script",
                        "--release",
                        "--",
                        "--words-json",
                        prepared.words_json.to_str().unwrap(),
                        "--mode",
                        "core",
                    ],
                )
            })
            .map_err(|err| {
                record_backend_failure(&fixture_dir, "sp1", &err.to_string()).ok();
                err
            })
            .ok()
        } else {
            None
        };

        let jolt = if args.run_jolt {
            benchmark_backend(args.runs, || {
                run_external_json_backend(
                    &args.jolt_root,
                    &[
                        "cargo",
                        "+1.94.1",
                        "run",
                        "-p",
                        "resolution-proof",
                        "--release",
                        "--",
                        "--words-json",
                        prepared.words_json.to_str().unwrap(),
                        "--target-dir",
                        prepared.fixture_dir.join("jolt-targets").to_str().unwrap(),
                    ],
                )
            })
            .map_err(|err| {
                record_backend_failure(&fixture_dir, "jolt", &err.to_string()).ok();
                err
            })
            .ok()
        } else {
            None
        };

        let zkwasm = if args.run_zkwasm {
            benchmark_backend(args.runs, || {
                run_zkwasm(
                    &args.zkwasm_example_root,
                    &args.zkwasm_root,
                    &args.zkwasm_guest_root,
                    &prepared.words_json,
                    &prepared.fixture_dir,
                    args.zkwasm_k,
                )
            })
            .map_err(|err| {
                record_backend_failure(&fixture_dir, "zkwasm", &err.to_string()).ok();
                err
            })
            .ok()
        } else {
            None
        };

        let summary = FixtureSummary {
            fixture: fixture.clone(),
            vars: prepared.instance.formula.num_vars,
            clauses: prepared.instance.formula.clauses.len(),
            resolution_steps: prepared.instance.proof.steps.len(),
            max_clause_width: prepared.instance.max_resolution_clause_width(),
            hyperplonk,
            sp1,
            jolt,
            zkwasm,
        };
        write_json(fixture_dir.join("summary.json"), &summary)?;
        summaries.push(summary);
    }

    write_json(args.output_dir.join("results/summary.json"), &summaries)?;
    write_summary_csv(args.output_dir.join("results/summary.csv"), &summaries)?;
    Ok(())
}

struct PreparedCase {
    fixture_dir: PathBuf,
    words_json: PathBuf,
    instance: ValidatedResolutionInstance,
}

fn prepare_case(args: &Args, fixture: &str) -> Result<PreparedCase, Box<dyn Error>> {
    let fixture_source_path = args.benchmark_root.join(fixture);
    let slug = fixture_slug(fixture);
    let fixture_dir = args.output_dir.join("fixtures").join(&slug);
    fs::create_dir_all(&fixture_dir)?;

    let source = fs::read_to_string(&fixture_source_path)?;
    fs::write(fixture_dir.join("source.c"), &source)?;

    let encoded = encode_c_source_to_cnf(&source)?;
    fs::write(fixture_dir.join("formula.cnf"), encoded.cnf.to_dimacs())?;

    let trace_path = fixture_dir.join("proof.TRACECHECK");
    run_picosat(
        &args.picosat,
        &fixture_dir.join("formula.cnf"),
        &trace_path,
        &fixture_dir.join("picosat.stdout"),
        &fixture_dir.join("picosat.stderr"),
    )?;

    let prf_path = fixture_dir.join("proof.prf");
    let unfold_path = fixture_dir.join("proof.prf.unfold");
    convert_trace_to_unfold(&args.zkunsat_root, &trace_path, &prf_path, &unfold_path)?;

    let unfolded = fs::read_to_string(&unfold_path)?;
    let instance = validate_resolution_instance_from_unfolded_trace(&encoded.cnf, &unfolded)?;
    let words = encode_witness_words(&instance.flat_witness());
    let words_json = fixture_dir.join("witness_words.json");
    write_json(words_json.clone(), &words)?;

    Ok(PreparedCase {
        fixture_dir,
        words_json,
        instance,
    })
}

fn run_hyperplonk(prepared: &PreparedCase) -> Result<SingleRunBench, Box<dyn Error>> {
    let prove_started = Instant::now();
    let proof = prove_hyperplonk_unsat(&prepared.instance)?;
    let prove_ms = elapsed_ms(prove_started);

    let verify_started = Instant::now();
    verify_hyperplonk_unsat(&prepared.instance.public_statement(), &proof)?;
    let verify_ms = elapsed_ms(verify_started);

    Ok(SingleRunBench {
        backend: "hyperplonk".to_owned(),
        setup_ms: 0.0,
        prove_ms,
        verify_ms,
        end_to_end_ms: prove_ms + verify_ms,
        proof_bytes: Some(proof.proof.len() as u64),
        num_vars: prepared.instance.commitment.num_vars,
        initial_clause_count: prepared.instance.commitment.num_clauses,
        resolution_steps: prepared.instance.proof.steps.len() as u32,
        max_clause_width: prepared.instance.max_resolution_clause_width(),
    })
}

fn run_external_json_backend(
    workdir: &Path,
    argv: &[&str],
) -> Result<SingleRunBench, Box<dyn Error>> {
    let output = Command::new(argv[0])
        .args(&argv[1..])
        .current_dir(workdir)
        .stderr(Stdio::inherit())
        .output()?;
    ensure_success(output.status, argv[0])?;
    Ok(serde_json::from_slice(&output.stdout)?)
}

fn run_zkwasm(
    zkwasm_example_root: &Path,
    zkwasm_root: &Path,
    guest_root: &Path,
    words_json: &Path,
    fixture_dir: &Path,
    k: u32,
) -> Result<SingleRunBench, Box<dyn Error>> {
    let output = Command::new("cargo")
        .arg("run")
        .arg("--release")
        .arg("--")
        .arg("--words-json")
        .arg(words_json)
        .arg("--work-dir")
        .arg(fixture_dir.join("zkwasm-work"))
        .arg("--zkwasm-root")
        .arg(zkwasm_root)
        .arg("--guest-root")
        .arg(guest_root)
        .arg("--k")
        .arg(k.to_string())
        .current_dir(zkwasm_example_root)
        .stderr(Stdio::inherit())
        .output()?;
    ensure_success(output.status, "resolution-proof-zkwasm")?;
    Ok(serde_json::from_slice(&output.stdout)?)
}

fn ensure_jolt_cli(jolt_root: &Path) -> Result<(), Box<dyn Error>> {
    ensure_success(
        Command::new("cargo")
            .arg("+1.94.1")
            .arg("build")
            .arg("-p")
            .arg("jolt")
            .arg("--release")
            .current_dir(jolt_root)
            .status()?,
        "jolt cli build",
    )
}

fn benchmark_backend<F>(runs: usize, mut f: F) -> Result<BenchAggregate, Box<dyn Error>>
where
    F: FnMut() -> Result<SingleRunBench, Box<dyn Error>>,
{
    let mut samples = Vec::with_capacity(runs);
    for _ in 0..runs {
        samples.push(f()?);
    }
    let backend = samples
        .first()
        .map(|sample| sample.backend.clone())
        .unwrap_or_default();
    Ok(BenchAggregate {
        backend,
        runs,
        median_end_to_end_ms: median(samples.iter().map(|sample| sample.end_to_end_ms).collect()),
        average_end_to_end_ms: average(samples.iter().map(|sample| sample.end_to_end_ms).collect()),
        median_prove_ms: median(samples.iter().map(|sample| sample.prove_ms).collect()),
        median_verify_ms: median(samples.iter().map(|sample| sample.verify_ms).collect()),
        median_setup_ms: median(samples.iter().map(|sample| sample.setup_ms).collect()),
        samples,
    })
}

impl Args {
    fn parse() -> Result<Self, Box<dyn Error>> {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let mut benchmark_root = manifest_dir.join(SYNTHETIC_FIXTURE_ROOT);
        let mut output_dir = manifest_dir.join("artifacts/resolution-zkvm-bench");
        let mut picosat = PathBuf::from(
            env::var("PICOSAT").unwrap_or_else(|_| "/tmp/picosat-965/picosat".to_owned()),
        );
        let mut fixtures = Vec::new();
        let mut runs = 1usize;
        let mut zkunsat_root = manifest_dir.join("../ZKUNSAT");
        let mut sp1_examples_root = manifest_dir.join("../external/sp1/examples");
        let mut jolt_root = manifest_dir.join("../external/jolt");
        let mut zkwasm_root = manifest_dir.join("../external/zkwasm");
        let mut zkwasm_example_root =
            manifest_dir.join("../external/zkwasm/examples/resolution-proof");
        let mut zkwasm_guest_root =
            manifest_dir.join("../external/zkwasm/examples/resolution-proof-guest");
        let mut zkwasm_k = 20u32;
        let mut run_hyperplonk = true;
        let mut run_sp1 = true;
        let mut run_jolt = true;
        let mut run_zkwasm = true;

        let mut args = env::args().skip(1);
        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--benchmark-root" => benchmark_root = PathBuf::from(next_arg(&mut args, &arg)?),
                "--output-dir" => output_dir = PathBuf::from(next_arg(&mut args, &arg)?),
                "--picosat" => picosat = PathBuf::from(next_arg(&mut args, &arg)?),
                "--fixture" => fixtures.push(next_arg(&mut args, &arg)?),
                "--runs" => runs = next_arg(&mut args, &arg)?.parse()?,
                "--zkunsat-root" => zkunsat_root = PathBuf::from(next_arg(&mut args, &arg)?),
                "--sp1-root" => sp1_examples_root = PathBuf::from(next_arg(&mut args, &arg)?),
                "--jolt-root" => jolt_root = PathBuf::from(next_arg(&mut args, &arg)?),
                "--zkwasm-root" => zkwasm_root = PathBuf::from(next_arg(&mut args, &arg)?),
                "--zkwasm-example-root" => {
                    zkwasm_example_root = PathBuf::from(next_arg(&mut args, &arg)?)
                }
                "--zkwasm-guest-root" => {
                    zkwasm_guest_root = PathBuf::from(next_arg(&mut args, &arg)?)
                }
                "--zkwasm-k" => zkwasm_k = next_arg(&mut args, &arg)?.parse()?,
                "--skip-hyperplonk" => run_hyperplonk = false,
                "--skip-sp1" => run_sp1 = false,
                "--skip-jolt" => run_jolt = false,
                "--skip-zkwasm" => run_zkwasm = false,
                "--help" | "-h" => {
                    print_usage();
                    std::process::exit(0);
                }
                other => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("unknown argument `{other}`"),
                    )
                    .into())
                }
            }
        }

        if fixtures.is_empty() {
            fixtures = RESOLUTION_ZKVM_FIXTURES
                .iter()
                .map(|fixture| (*fixture).to_owned())
                .collect();
        }

        Ok(Self {
            benchmark_root,
            output_dir,
            picosat,
            fixtures,
            runs,
            zkunsat_root,
            sp1_examples_root,
            jolt_root,
            zkwasm_root,
            zkwasm_example_root,
            zkwasm_guest_root,
            zkwasm_k,
            run_hyperplonk,
            run_sp1,
            run_jolt,
            run_zkwasm,
        })
    }
}

fn print_usage() {
    eprintln!(
        "usage: cargo run --release --features backend-hyperplonk --example bench_resolution_zkvms -- [options]\n\
         --benchmark-root <path>   UNSAT fixture root (default: tests/fixtures)\n\
         --output-dir <path>       artifact root\n\
         --picosat <path>          picosat binary compiled with trace support\n\
         --fixture <path>          UNSAT fixture relative path, repeatable\n\
         --runs <n>                proving runs per backend (default: 1)\n\
         --zkunsat-root <path>     ZKUNSAT repo root\n\
         --sp1-root <path>         SP1 examples root\n\
         --jolt-root <path>        Jolt repo root\n\
         --zkwasm-root <path>      zkWASM repo root\n\
         --zkwasm-example-root <path>\n\
         --zkwasm-guest-root <path>\n\
         --zkwasm-k <n>\n\
         --skip-hyperplonk|--skip-sp1|--skip-jolt|--skip-zkwasm"
    );
}

fn next_arg(args: &mut impl Iterator<Item = String>, flag: &str) -> Result<String, io::Error> {
    args.next().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("missing value for `{flag}`"),
        )
    })
}

fn run_picosat(
    picosat: &Path,
    cnf_path: &Path,
    trace_path: &Path,
    stdout_path: &Path,
    stderr_path: &Path,
) -> Result<(), Box<dyn Error>> {
    let status = Command::new(picosat)
        .arg("-T")
        .arg(trace_path)
        .arg(cnf_path)
        .stdout(Stdio::from(fs::File::create(stdout_path)?))
        .stderr(Stdio::from(fs::File::create(stderr_path)?))
        .status()?;
    if status.code() != Some(20) {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!("picosat expected UNSAT for {}", cnf_path.display()),
        )
        .into());
    }
    Ok(())
}

fn convert_trace_to_unfold(
    zkunsat_root: &Path,
    trace_path: &Path,
    prf_path: &Path,
    unfold_path: &Path,
) -> Result<(), Box<dyn Error>> {
    let sort_script = zkunsat_root.join("prover_backend/Sort.py");
    let unfold_script = zkunsat_root.join("prover_backend/unfold_proof.py");

    ensure_success(
        Command::new("python3")
            .arg(&sort_script)
            .arg(trace_path)
            .stdout(Stdio::from(fs::File::create(prf_path)?))
            .stderr(Stdio::inherit())
            .status()?,
        "Sort.py",
    )?;
    if unfold_path.exists() {
        fs::remove_file(unfold_path)?;
    }
    ensure_success(
        Command::new("python3")
            .arg(&unfold_script)
            .arg(prf_path)
            .current_dir(zkunsat_root)
            .stderr(Stdio::inherit())
            .status()?,
        "unfold_proof.py",
    )?;
    Ok(())
}

fn ensure_success(status: ExitStatus, label: &str) -> Result<(), Box<dyn Error>> {
    if status.success() {
        Ok(())
    } else {
        Err(io::Error::new(
            io::ErrorKind::Other,
            format!("{label} failed with exit code {:?}", status.code()),
        )
        .into())
    }
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), Box<dyn Error>> {
    fs::write(path, serde_json::to_vec_pretty(value)?)?;
    Ok(())
}

fn record_backend_failure(
    fixture_dir: &Path,
    backend: &str,
    error: &str,
) -> Result<(), Box<dyn Error>> {
    fs::write(fixture_dir.join(format!("{backend}.failed.txt")), error)?;
    Ok(())
}

fn write_summary_csv(path: PathBuf, rows: &[FixtureSummary]) -> Result<(), Box<dyn Error>> {
    let mut out = String::from(
        "fixture,vars,clauses,resolution_steps,max_clause_width,backend,runs,median_end_to_end_ms,median_setup_ms,median_prove_ms,median_verify_ms\n",
    );
    for row in rows {
        for bench in [&row.hyperplonk, &row.sp1, &row.jolt, &row.zkwasm]
            .into_iter()
            .flatten()
        {
            out.push_str(&format!(
                "{},{},{},{},{},{},{},{:.3},{:.3},{:.3},{:.3}\n",
                row.fixture,
                row.vars,
                row.clauses,
                row.resolution_steps,
                row.max_clause_width,
                bench.backend,
                bench.runs,
                bench.median_end_to_end_ms,
                bench.median_setup_ms,
                bench.median_prove_ms,
                bench.median_verify_ms,
            ));
        }
    }
    fs::write(path, out)?;
    Ok(())
}

fn fixture_slug(fixture: &str) -> String {
    fixture
        .replace('/', "__")
        .replace('.', "_")
        .replace('-', "_")
}

fn elapsed_ms(started: Instant) -> f64 {
    started.elapsed().as_secs_f64() * 1_000.0
}

fn median(mut values: Vec<f64>) -> f64 {
    values.sort_by(|a, b| a.partial_cmp(b).unwrap());
    values[values.len() / 2]
}

fn average(values: Vec<f64>) -> f64 {
    values.iter().sum::<f64>() / values.len() as f64
}
