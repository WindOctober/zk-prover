#![cfg(all(feature = "backend-hyperplonk", feature = "backend-plonky3"))]

use std::{
    env,
    error::Error,
    fs, io,
    net::TcpListener,
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Stdio},
    thread,
    time::{Duration, Instant},
};

use serde::Serialize;
use zk_prover::{
    backend::{
        halo2::hyperplonk::{
            prove_unsat as prove_hyperplonk_unsat, verify_unsat as verify_hyperplonk_unsat,
        },
        phase2::{validate_resolution_instance_from_unfolded_trace, UnsatPublicStatement},
        plonky3::air::{
            prove_unsat as prove_plonky3_unsat,
            prove_unsat_committed as prove_plonky3_unsat_committed,
            verify_unsat as verify_plonky3_unsat,
            verify_unsat_committed as verify_plonky3_unsat_committed,
        },
    },
    encode_c_source_to_cnf, SVCOMP_BENCHMARK_ROOT, SVCOMP_FIXTURES, SYNTHETIC_FIXTURE_ROOT,
    UNSAT_PIPELINE_FIXTURES,
};

#[derive(Debug, Clone)]
struct Args {
    benchmark_root: PathBuf,
    output_dir: PathBuf,
    picosat: PathBuf,
    fixtures: Vec<String>,
    runs: usize,
    zkunsat_root: Option<PathBuf>,
    zkunsat_bin: Option<PathBuf>,
    zkunsat_threads: Option<usize>,
    skip_hyperplonk: bool,
    skip_plonky3: bool,
    skip_zkunsat: bool,
    check_formula_commitment: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "UPPERCASE")]
enum SolverOutcome {
    Sat,
    Unsat,
}

#[derive(Debug, Clone, Serialize)]
struct EncodeMetadata {
    fixture: String,
    source_path: String,
    encode_ms: f64,
    steps: u32,
    blocks: u32,
    program_vars: u32,
    nondet_symbols: u32,
    cnf_vars: u32,
    cnf_clauses: usize,
    cnf_sha256: String,
}

#[derive(Debug, Clone, Serialize)]
struct SolverMetadata {
    outcome: SolverOutcome,
    exit_code: i32,
    solve_ms: f64,
    trace_path: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
struct WitnessMetadata {
    resolution_steps: usize,
    max_clause_width: u32,
    public_statement: UnsatPublicStatement,
}

#[derive(Debug, Clone, Serialize)]
struct BenchMetadata {
    backend: String,
    threads: usize,
    runs: usize,
    samples_ms: Vec<f64>,
    median_ms: f64,
    average_ms: f64,
    last_ms: f64,
    verify_samples_ms: Option<Vec<f64>>,
    median_verify_ms: Option<f64>,
    average_verify_ms: Option<f64>,
    last_verify_ms: Option<f64>,
    proof_bytes: Option<usize>,
}

#[derive(Debug, Clone)]
struct FixtureResult {
    fixture: String,
    vars: u32,
    clauses: usize,
    resolution_steps: Option<usize>,
    hyperplonk: Option<BenchMetadata>,
    plonky3: Option<BenchMetadata>,
    zkunsat: Option<BenchMetadata>,
}

#[derive(Debug, Clone, Copy)]
enum Preset {
    Svcomp,
    SyntheticUnsat,
}

impl Preset {
    fn parse(raw: &str) -> Result<Self, io::Error> {
        match raw {
            "svcomp" => Ok(Self::Svcomp),
            "synthetic-unsat" => Ok(Self::SyntheticUnsat),
            other => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("unknown preset `{other}`"),
            )),
        }
    }

    fn benchmark_root(self, manifest_dir: &Path) -> PathBuf {
        match self {
            Self::Svcomp => manifest_dir.join(SVCOMP_BENCHMARK_ROOT),
            Self::SyntheticUnsat => manifest_dir.join(SYNTHETIC_FIXTURE_ROOT),
        }
    }

    fn default_output_dir(self, manifest_dir: &Path) -> PathBuf {
        match self {
            Self::Svcomp => manifest_dir.join("artifacts/svcomp-pipeline-bench"),
            Self::SyntheticUnsat => manifest_dir.join("artifacts/unsat-bench"),
        }
    }

    fn fixtures(self) -> &'static [&'static str] {
        match self {
            Self::Svcomp => SVCOMP_FIXTURES,
            Self::SyntheticUnsat => UNSAT_PIPELINE_FIXTURES,
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse()?;
    let rayon_threads = current_thread_count();

    println!(
        "benchmark_root={} output_dir={} picosat={} rayon_threads={} runs={}",
        args.benchmark_root.display(),
        args.output_dir.display(),
        args.picosat.display(),
        rayon_threads,
        args.runs,
    );

    fs::create_dir_all(args.output_dir.join("fixtures"))?;
    fs::create_dir_all(args.output_dir.join("results"))?;

    let mut fixture_results = Vec::new();

    for fixture in &args.fixtures {
        let fixture_source_path = args.benchmark_root.join(fixture);
        let source = fs::read_to_string(&fixture_source_path)?;
        let slug = fixture_slug(fixture);
        let fixture_dir = args.output_dir.join("fixtures").join(&slug);
        fs::create_dir_all(&fixture_dir)?;

        let encode_started = Instant::now();
        let encoded = encode_c_source_to_cnf(&source)?;
        let encode_ms = elapsed_ms(encode_started);

        fs::write(fixture_dir.join("source.c"), &source)?;
        fs::write(fixture_dir.join("formula.cnf"), encoded.cnf.to_dimacs())?;

        let encode_meta = EncodeMetadata {
            fixture: fixture.clone(),
            source_path: fixture_source_path.display().to_string(),
            encode_ms,
            steps: encoded.steps,
            blocks: encoded.blocks,
            program_vars: encoded.program_vars,
            nondet_symbols: encoded.nondet_symbols,
            cnf_vars: encoded.cnf.num_vars,
            cnf_clauses: encoded.cnf.clauses.len(),
            cnf_sha256: hex_string(&encoded.cnf.sha256_digest()),
        };
        write_json(fixture_dir.join("encode_summary.json"), &encode_meta)?;

        let trace_path = fixture_dir.join("proof.TRACECHECK");
        let solver_meta = run_picosat(
            &args.picosat,
            &fixture_dir.join("formula.cnf"),
            &trace_path,
            &fixture_dir.join("picosat.stdout"),
            &fixture_dir.join("picosat.stderr"),
        )?;
        write_json(fixture_dir.join("solver_result.json"), &solver_meta)?;

        match solver_meta.outcome {
            SolverOutcome::Sat => {
                println!(
                    "[SAT] {} vars={} clauses={} encode_ms={:.3} solve_ms={:.3}",
                    fixture,
                    encoded.cnf.num_vars,
                    encoded.cnf.clauses.len(),
                    encode_ms,
                    solver_meta.solve_ms,
                );
                fixture_results.push(FixtureResult {
                    fixture: fixture.clone(),
                    vars: encoded.cnf.num_vars,
                    clauses: encoded.cnf.clauses.len(),
                    resolution_steps: None,
                    hyperplonk: None,
                    plonky3: None,
                    zkunsat: None,
                });
            }
            SolverOutcome::Unsat => {
                let zkunsat_root = args.zkunsat_root.as_ref().ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "UNSAT proof unfolding requires --zkunsat-root so the local Sort.py/unfold_proof.py scripts can run",
                    )
                })?;
                let prf_path = fixture_dir.join("proof.prf");
                let unfold_path = fixture_dir.join("proof.prf.unfold");
                convert_trace_to_unfold(zkunsat_root, &trace_path, &prf_path, &unfold_path)?;

                let unfolded = fs::read_to_string(&unfold_path)?;
                let instance =
                    validate_resolution_instance_from_unfolded_trace(&encoded.cnf, &unfolded)?;
                write_json(fixture_dir.join("resolution_proof.json"), &instance.proof)?;
                write_json(
                    fixture_dir.join("validated_resolution_instance.json"),
                    &instance,
                )?;
                let witness_meta = WitnessMetadata {
                    resolution_steps: instance.proof.steps.len(),
                    max_clause_width: instance.commitment.max_clause_width,
                    public_statement: instance.public_statement(),
                };
                write_json(fixture_dir.join("witness_summary.json"), &witness_meta)?;

                println!(
                    "[UNSAT] {} vars={} clauses={} steps={} encode_ms={:.3} solve_ms={:.3}",
                    fixture,
                    encoded.cnf.num_vars,
                    encoded.cnf.clauses.len(),
                    instance.proof.steps.len(),
                    encode_ms,
                    solver_meta.solve_ms,
                );

                let hyperplonk_meta = if args.skip_hyperplonk {
                    None
                } else {
                    match (|| -> Result<BenchMetadata, Box<dyn Error>> {
                        let (hyperplonk_proof, hyperplonk_bench) =
                            benchmark(args.runs, || prove_hyperplonk_unsat(&instance))
                                .map_err(|err| Box::new(err) as Box<dyn Error>)?;
                        let (_, hyperplonk_verify_bench) = benchmark(args.runs, || {
                            verify_hyperplonk_unsat(&instance.public_statement(), &hyperplonk_proof)
                        })
                        .map_err(|err| Box::new(err) as Box<dyn Error>)?;
                        Ok(bench_metadata(
                            "hyperplonk",
                            rayon_threads,
                            args.runs,
                            &hyperplonk_bench,
                            Some(&hyperplonk_verify_bench),
                            Some(hyperplonk_proof.proof.len()),
                        ))
                    })() {
                        Ok(meta) => {
                            write_json(
                                fixture_dir
                                    .join(format!("bench_hyperplonk_threads_{rayon_threads}.json")),
                                &meta,
                            )?;
                            Some(meta)
                        }
                        Err(err) => {
                            record_backend_failure(
                                &fixture_dir,
                                "hyperplonk",
                                rayon_threads,
                                &err.to_string(),
                            )?;
                            eprintln!(
                                "[BACKEND-FAIL] fixture={} backend=hyperplonk threads={} error={}",
                                fixture, rayon_threads, err
                            );
                            None
                        }
                    }
                };

                let plonky3_meta = if args.skip_plonky3 {
                    None
                } else {
                    match (|| -> Result<BenchMetadata, Box<dyn Error>> {
                        let (plonky3_proof, plonky3_bench) = benchmark(args.runs, || {
                            if args.check_formula_commitment {
                                prove_plonky3_unsat_committed(&instance)
                            } else {
                                prove_plonky3_unsat(&instance)
                            }
                        })
                        .map_err(|err| Box::new(err) as Box<dyn Error>)?;
                        let plonky3_proof_bytes = postcard::to_allocvec(&plonky3_proof.proof)
                            .map_err(|err| Box::new(err) as Box<dyn Error>)?
                            .len();
                        let (_, plonky3_verify_bench) = benchmark(args.runs, || {
                            if args.check_formula_commitment {
                                verify_plonky3_unsat_committed(
                                    &instance.committed_public_statement(),
                                    &plonky3_proof,
                                )
                            } else {
                                verify_plonky3_unsat(&instance.public_statement(), &plonky3_proof)
                            }
                        })
                        .map_err(|err| Box::new(err) as Box<dyn Error>)?;
                        Ok(bench_metadata(
                            "plonky3",
                            rayon_threads,
                            args.runs,
                            &plonky3_bench,
                            Some(&plonky3_verify_bench),
                            Some(plonky3_proof_bytes),
                        ))
                    })() {
                        Ok(meta) => {
                            write_json(
                                fixture_dir
                                    .join(format!("bench_plonky3_threads_{rayon_threads}.json")),
                                &meta,
                            )?;
                            Some(meta)
                        }
                        Err(err) => {
                            record_backend_failure(
                                &fixture_dir,
                                "plonky3",
                                rayon_threads,
                                &err.to_string(),
                            )?;
                            eprintln!(
                                "[BACKEND-FAIL] fixture={} backend=plonky3 threads={} error={}",
                                fixture, rayon_threads, err
                            );
                            None
                        }
                    }
                };

                let zkunsat_meta = if args.skip_zkunsat {
                    None
                } else {
                    let zkunsat_threads = args.zkunsat_threads.unwrap_or(rayon_threads);
                    match benchmark_zkunsat(
                        args.runs,
                        zkunsat_root,
                        args.zkunsat_bin.as_deref(),
                        &unfold_path,
                        zkunsat_threads,
                        &fixture_dir,
                    ) {
                        Ok(bench) => {
                            let meta = bench_metadata(
                                "zkunsat",
                                zkunsat_threads,
                                args.runs,
                                &bench,
                                None,
                                None,
                            );
                            write_json(
                                fixture_dir
                                    .join(format!("bench_zkunsat_threads_{zkunsat_threads}.json")),
                                &meta,
                            )?;
                            Some(meta)
                        }
                        Err(err) => {
                            record_backend_failure(
                                &fixture_dir,
                                "zkunsat",
                                zkunsat_threads,
                                &err.to_string(),
                            )?;
                            eprintln!(
                                "[BACKEND-FAIL] fixture={} backend=zkunsat threads={} error={}",
                                fixture, zkunsat_threads, err
                            );
                            None
                        }
                    }
                };

                fixture_results.push(FixtureResult {
                    fixture: fixture.clone(),
                    vars: encoded.cnf.num_vars,
                    clauses: encoded.cnf.clauses.len(),
                    resolution_steps: Some(instance.proof.steps.len()),
                    hyperplonk: hyperplonk_meta,
                    plonky3: plonky3_meta,
                    zkunsat: zkunsat_meta,
                });
            }
        }
    }

    write_summary_csv(
        args.output_dir
            .join("results")
            .join(format!("summary_threads_{rayon_threads}.csv")),
        &fixture_results,
    )?;

    Ok(())
}

impl Args {
    fn parse() -> Result<Self, Box<dyn Error>> {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let mut preset = Preset::Svcomp;
        let mut benchmark_root = preset.benchmark_root(&manifest_dir);
        let mut output_dir = preset.default_output_dir(&manifest_dir);
        let mut picosat = PathBuf::from(
            env::var("PICOSAT").unwrap_or_else(|_| "/tmp/picosat-965/picosat".to_owned()),
        );
        let mut fixtures = Vec::new();
        let mut runs = 3usize;
        let mut zkunsat_root = Some(manifest_dir.join("../ZKUNSAT"));
        let mut zkunsat_bin = None;
        let mut zkunsat_threads = None;
        let mut skip_hyperplonk = false;
        let mut skip_plonky3 = false;
        let mut skip_zkunsat = false;
        let mut check_formula_commitment = false;
        let mut benchmark_root_overridden = false;
        let mut output_dir_overridden = false;

        let mut args = env::args().skip(1);
        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--preset" => {
                    preset = Preset::parse(&next_arg(&mut args, &arg)?)?;
                    if !benchmark_root_overridden {
                        benchmark_root = preset.benchmark_root(&manifest_dir);
                    }
                    if !output_dir_overridden {
                        output_dir = preset.default_output_dir(&manifest_dir);
                    }
                }
                "--benchmark-root" => {
                    benchmark_root = PathBuf::from(next_arg(&mut args, &arg)?);
                    benchmark_root_overridden = true;
                }
                "--output-dir" => {
                    output_dir = PathBuf::from(next_arg(&mut args, &arg)?);
                    output_dir_overridden = true;
                }
                "--picosat" => picosat = PathBuf::from(next_arg(&mut args, &arg)?),
                "--fixture" => fixtures.push(next_arg(&mut args, &arg)?),
                "--runs" => runs = next_arg(&mut args, &arg)?.parse()?,
                "--zkunsat-root" => zkunsat_root = Some(PathBuf::from(next_arg(&mut args, &arg)?)),
                "--zkunsat-bin" => zkunsat_bin = Some(PathBuf::from(next_arg(&mut args, &arg)?)),
                "--zkunsat-threads" => zkunsat_threads = Some(next_arg(&mut args, &arg)?.parse()?),
                "--skip-hyperplonk" => skip_hyperplonk = true,
                "--skip-plonky3" => skip_plonky3 = true,
                "--skip-zkunsat" => skip_zkunsat = true,
                "--check-formula-commitment" => check_formula_commitment = true,
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
            fixtures = preset
                .fixtures()
                .iter()
                .map(|fixture| (*fixture).to_owned())
                .collect();
        }
        if skip_zkunsat {
            zkunsat_bin = None;
        }
        if runs == 0 {
            return Err(
                io::Error::new(io::ErrorKind::InvalidInput, "`--runs` must be at least 1").into(),
            );
        }

        Ok(Self {
            benchmark_root,
            output_dir,
            picosat,
            fixtures,
            runs,
            zkunsat_root,
            zkunsat_bin,
            zkunsat_threads,
            skip_hyperplonk,
            skip_plonky3,
            skip_zkunsat,
            check_formula_commitment,
        })
    }
}

fn print_usage() {
    eprintln!(
        "usage: cargo run --release --features proof-backends --example bench_unsat_pipeline -- [options]\n\
         --preset <svcomp|synthetic-unsat>\n\
         --benchmark-root <path>   benchmark fixture root\n\
         --output-dir <path>       artifact root\n\
         --picosat <path>          picosat binary compiled with trace support\n\
         --fixture <path>          fixture relative path, repeatable\n\
         --runs <n>                proving runs per backend (default: 3)\n\
         --zkunsat-root <path>     ZKUNSAT repo root\n\
         --zkunsat-bin <path>      ZKUNSAT binary path (default: <root>/build/test)\n\
         --zkunsat-threads <n>     ZKUNSAT worker threads (default: current rayon thread count)\n\
         --skip-hyperplonk         do not benchmark HyperPlonk\n\
         --skip-plonky3            do not benchmark the Plonky3 backend\n\
         --skip-zkunsat            do not benchmark ZKUNSAT\n\
         --check-formula-commitment enable Plonky3 private-formula commitment constraints\n\
         \n\
         presets:\n\
         svcomp           official SV-COMP slice; benchmarks encode+solve and only proves UNSAT cases when any exist\n\
         synthetic-unsat  local UNSAT-heavy fixtures for resolution-proof benchmarking"
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
) -> Result<SolverMetadata, Box<dyn Error>> {
    let started = Instant::now();
    let status = Command::new(picosat)
        .arg("-T")
        .arg(trace_path)
        .arg(cnf_path)
        .stdout(Stdio::from(fs::File::create(stdout_path)?))
        .stderr(Stdio::from(fs::File::create(stderr_path)?))
        .status()?;
    let solve_ms = elapsed_ms(started);
    let exit_code = status.code().unwrap_or(-1);
    let outcome = match exit_code {
        10 => SolverOutcome::Sat,
        20 => SolverOutcome::Unsat,
        _ => {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                format!(
                    "picosat failed for {} with exit code {:?}",
                    cnf_path.display(),
                    status.code()
                ),
            )
            .into())
        }
    };

    Ok(SolverMetadata {
        outcome,
        exit_code,
        solve_ms,
        trace_path: (outcome == SolverOutcome::Unsat).then(|| trace_path.display().to_string()),
    })
}

fn convert_trace_to_unfold(
    zkunsat_root: &Path,
    trace_path: &Path,
    prf_path: &Path,
    unfold_path: &Path,
) -> Result<(), Box<dyn Error>> {
    let sort_script = zkunsat_root.join("prover_backend/Sort.py");
    let unfold_script = zkunsat_root.join("prover_backend/unfold_proof.py");

    let sort_status = Command::new("python3")
        .arg(&sort_script)
        .arg(trace_path)
        .stdout(Stdio::from(fs::File::create(prf_path)?))
        .stderr(Stdio::inherit())
        .status()?;
    ensure_success(sort_status, "Sort.py")?;

    if unfold_path.exists() {
        fs::remove_file(unfold_path)?;
    }
    let unfold_status = Command::new("python3")
        .arg(&unfold_script)
        .arg(prf_path)
        .current_dir(zkunsat_root)
        .stderr(Stdio::inherit())
        .status()?;
    ensure_success(unfold_status, "unfold_proof.py")?;
    Ok(())
}

fn benchmark<T, E, F>(runs: usize, mut f: F) -> Result<(T, Vec<f64>), E>
where
    F: FnMut() -> Result<T, E>,
{
    let mut samples = Vec::with_capacity(runs);
    let mut last = None;

    for _ in 0..runs {
        let started = Instant::now();
        let value = f()?;
        samples.push(elapsed_ms(started));
        last = Some(value);
    }

    Ok((last.expect("benchmark requires at least one run"), samples))
}

fn benchmark_zkunsat(
    runs: usize,
    zkunsat_root: &Path,
    zkunsat_bin_override: Option<&Path>,
    proof_path: &Path,
    threads: usize,
    fixture_dir: &Path,
) -> Result<Vec<f64>, Box<dyn Error>> {
    let binary = zkunsat_bin_override
        .map(PathBuf::from)
        .unwrap_or_else(|| zkunsat_root.join("build/test"));
    let mut samples = Vec::with_capacity(runs);

    for run in 0..runs {
        let port = free_port_range_start(threads)?;
        let party1_log =
            fixture_dir.join(format!("zkunsat_party1_threads_{threads}_run_{run}.log"));
        let party2_log =
            fixture_dir.join(format!("zkunsat_party2_threads_{threads}_run_{run}.log"));
        let envs = zkunsat_env(zkunsat_root, threads);

        let started = Instant::now();
        let mut party1 = Command::new(&binary)
            .arg("1")
            .arg(port.to_string())
            .arg("127.0.0.1")
            .arg(proof_path)
            .current_dir(zkunsat_root)
            .envs(envs.clone())
            .stdout(Stdio::from(fs::File::create(&party1_log)?))
            .stderr(Stdio::from(
                fs::File::options().append(true).open(&party1_log)?,
            ))
            .spawn()?;

        thread::sleep(Duration::from_millis(250));

        let mut party2 = Command::new(&binary)
            .arg("2")
            .arg(port.to_string())
            .arg("127.0.0.1")
            .arg(proof_path)
            .current_dir(zkunsat_root)
            .envs(envs)
            .stdout(Stdio::from(fs::File::create(&party2_log)?))
            .stderr(Stdio::from(
                fs::File::options().append(true).open(&party2_log)?,
            ))
            .spawn()?;

        let status1 = party1.wait()?;
        let status2 = party2.wait()?;
        ensure_success(status1, "zkunsat party 1")?;
        ensure_success(status2, "zkunsat party 2")?;

        let log1 = fs::read_to_string(&party1_log)?;
        let log2 = fs::read_to_string(&party2_log)?;
        if !(log1.contains("----end----") && log2.contains("----end----")) {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                format!(
                    "zkunsat run {run} did not finish cleanly for {}",
                    proof_path.display()
                ),
            )
            .into());
        }

        samples.push(elapsed_ms(started));
    }

    Ok(samples)
}

fn zkunsat_env(zkunsat_root: &Path, threads: usize) -> Vec<(String, String)> {
    let local_prefix = zkunsat_root.join(".local");
    let include_dir = local_prefix.join("include");
    let lib_dir = local_prefix.join("lib");
    let include_path = format!("{}:/usr/include/x86_64-linux-gnu", include_dir.display());
    let lib_path = lib_dir.display().to_string();
    vec![
        (
            "ZKUNSAT_ROOT".to_owned(),
            zkunsat_root.display().to_string(),
        ),
        (
            "LOCAL_PREFIX".to_owned(),
            local_prefix.display().to_string(),
        ),
        ("EMP_TOOL_DIR".to_owned(), include_dir.display().to_string()),
        ("EMP_ZK_DIR".to_owned(), include_dir.display().to_string()),
        (
            "CMAKE_PREFIX_PATH".to_owned(),
            local_prefix.display().to_string(),
        ),
        ("CPATH".to_owned(), include_path),
        ("LIBRARY_PATH".to_owned(), lib_path.clone()),
        ("LD_LIBRARY_PATH".to_owned(), lib_path),
        (
            "PKG_CONFIG_PATH".to_owned(),
            lib_dir.join("pkgconfig").display().to_string(),
        ),
        ("ZKUNSAT_THREADS".to_owned(), threads.to_string()),
    ]
}

fn write_summary_csv(path: PathBuf, rows: &[FixtureResult]) -> Result<(), Box<dyn Error>> {
    let mut out = String::from(
        "fixture,status,vars,clauses,resolution_steps,backend,threads,runs,median_prove_ms,avg_prove_ms,last_prove_ms,median_verify_ms,avg_verify_ms,last_verify_ms,proof_bytes\n",
    );

    for row in rows {
        if row.resolution_steps.is_none() {
            out.push_str(&format!(
                "{},SAT,{},{},,,,,,,,,,,\n",
                row.fixture, row.vars, row.clauses,
            ));
            continue;
        }

        let resolution_steps = row.resolution_steps.unwrap();
        for bench in [&row.hyperplonk, &row.plonky3, &row.zkunsat]
            .into_iter()
            .flatten()
        {
            out.push_str(&format!(
                "{},UNSAT,{},{},{},{},{},{},{:.3},{:.3},{:.3},{},{},{},{}\n",
                row.fixture,
                row.vars,
                row.clauses,
                resolution_steps,
                bench.backend,
                bench.threads,
                bench.runs,
                bench.median_ms,
                bench.average_ms,
                bench.last_ms,
                format_opt_ms(bench.median_verify_ms),
                format_opt_ms(bench.average_verify_ms),
                format_opt_ms(bench.last_verify_ms),
                bench
                    .proof_bytes
                    .map(|value| value.to_string())
                    .unwrap_or_default(),
            ));
        }
    }

    fs::write(path, out)?;
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
    threads: usize,
    error: &str,
) -> Result<(), Box<dyn Error>> {
    let path = fixture_dir.join(format!("bench_{backend}_threads_{threads}.failed.txt"));
    fs::write(path, error)?;
    Ok(())
}

fn bench_metadata(
    backend: &str,
    threads: usize,
    runs: usize,
    samples: &[f64],
    verify_samples: Option<&[f64]>,
    proof_bytes: Option<usize>,
) -> BenchMetadata {
    BenchMetadata {
        backend: backend.to_owned(),
        threads,
        runs,
        samples_ms: samples.to_vec(),
        median_ms: median_ms(samples),
        average_ms: average_ms(samples),
        last_ms: *samples.last().unwrap_or(&0.0),
        verify_samples_ms: verify_samples.map(|samples| samples.to_vec()),
        median_verify_ms: verify_samples.map(median_ms),
        average_verify_ms: verify_samples.map(average_ms),
        last_verify_ms: verify_samples.and_then(|samples| samples.last().copied()),
        proof_bytes,
    }
}

fn format_opt_ms(value: Option<f64>) -> String {
    value.map(|value| format!("{value:.3}")).unwrap_or_default()
}

fn median_ms(samples: &[f64]) -> f64 {
    let mut sorted = samples.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
    sorted[sorted.len() / 2]
}

fn average_ms(samples: &[f64]) -> f64 {
    samples.iter().sum::<f64>() / samples.len() as f64
}

fn elapsed_ms(started: Instant) -> f64 {
    started.elapsed().as_secs_f64() * 1000.0
}

fn fixture_slug(fixture: &str) -> String {
    fixture
        .replace('/', "__")
        .replace('.', "_")
        .replace('-', "_")
}

fn current_thread_count() -> usize {
    env::var("RAYON_NUM_THREADS")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|value| *value > 0)
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|value| value.get())
                .unwrap_or(1)
        })
}

fn free_port_range_start(width: usize) -> Result<u16, Box<dyn Error>> {
    for _ in 0..64 {
        let seed = TcpListener::bind("127.0.0.1:0")?;
        let base = seed.local_addr()?.port();
        drop(seed);

        let mut reserved = Vec::with_capacity(width);
        let mut ok = true;

        for offset in 0..width {
            let Some(port) = base.checked_add(offset as u16) else {
                ok = false;
                break;
            };
            match TcpListener::bind(("127.0.0.1", port)) {
                Ok(listener) => reserved.push(listener),
                Err(_) => {
                    ok = false;
                    break;
                }
            }
        }

        if ok {
            drop(reserved);
            return Ok(base);
        }
    }

    Err(io::Error::new(
        io::ErrorKind::AddrNotAvailable,
        format!("failed to reserve a contiguous localhost port range of width {width}"),
    )
    .into())
}

fn hex_string(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(&mut out, "{byte:02x}");
    }
    out
}
