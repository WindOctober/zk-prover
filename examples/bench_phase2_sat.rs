use std::{
    env,
    error::Error,
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

#[cfg(all(feature = "backend-solver", feature = "backend-plonky3"))]
fn main() -> Result<(), Box<dyn Error>> {
    use zk_prover::{
        backend::{
            phase2::{solve_formula, SatOutcome},
            plonky3::air::{prove_sat, verify_sat},
        },
        encode_c_source_to_cnf,
    };

    let args = Args::parse()?;
    println!("fixture,status,vars,clauses,runs,median_prove_ms,median_verify_ms,proof_bytes");

    for fixture in &args.fixtures {
        let source_path = args.benchmark_root.join(fixture);
        let source = fs::read_to_string(&source_path)
            .map_err(|err| format!("failed to read {}: {err}", source_path.display()))?;
        let encoded = encode_c_source_to_cnf(&source)?;
        let SatOutcome::Sat(instance) = solve_formula(&encoded.cnf)? else {
            println!(
                "{fixture},not-sat,{},{},{},,,,",
                encoded.cnf.num_vars,
                encoded.cnf.clauses.len(),
                args.runs
            );
            continue;
        };

        let mut prove_samples = Vec::with_capacity(args.runs);
        let mut verify_samples = Vec::with_capacity(args.runs);
        let mut proof_bytes = 0usize;
        for _ in 0..args.runs {
            let prove_started = Instant::now();
            let proof = prove_sat(&instance)?;
            prove_samples.push(elapsed_ms(prove_started));

            proof_bytes = postcard::to_allocvec(&proof.proof)?.len();

            let verify_started = Instant::now();
            verify_sat(&instance, &proof)?;
            verify_samples.push(elapsed_ms(verify_started));
        }

        println!(
            "{fixture},SAT,{},{},{},{:.3},{:.3},{}",
            encoded.cnf.num_vars,
            encoded.cnf.clauses.len(),
            args.runs,
            median(&prove_samples),
            median(&verify_samples),
            proof_bytes
        );
    }

    Ok(())
}

#[cfg(not(all(feature = "backend-solver", feature = "backend-plonky3")))]
fn main() {
    eprintln!("bench_phase2_sat requires `--features backend-solver,backend-plonky3`");
    std::process::exit(1);
}

#[derive(Debug)]
struct Args {
    benchmark_root: PathBuf,
    fixtures: Vec<String>,
    runs: usize,
}

impl Args {
    fn parse() -> Result<Self, Box<dyn Error>> {
        let mut benchmark_root = PathBuf::from("benchmarks/svcomp-initial");
        let mut fixtures = Vec::new();
        let mut runs = 1usize;
        let mut args = env::args().skip(1);

        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--benchmark-root" => benchmark_root = PathBuf::from(next_arg(&mut args, &arg)?),
                "--fixture" => fixtures.push(next_arg(&mut args, &arg)?),
                "--runs" => runs = next_arg(&mut args, &arg)?.parse()?,
                "--help" | "-h" => {
                    print_usage();
                    std::process::exit(0);
                }
                other => return Err(format!("unknown argument `{other}`").into()),
            }
        }

        if fixtures.is_empty() {
            fixtures.push("vendor/sv-benchmarks/c/validation-crafted/if.c".to_owned());
            fixtures.push("vendor/sv-benchmarks/c/validation-crafted/ternary.c".to_owned());
        }
        if runs == 0 {
            return Err("runs must be positive".into());
        }

        Ok(Self {
            benchmark_root: absolutize(&benchmark_root)?,
            fixtures,
            runs,
        })
    }
}

fn next_arg(args: &mut impl Iterator<Item = String>, flag: &str) -> Result<String, Box<dyn Error>> {
    args.next()
        .ok_or_else(|| format!("{flag} requires a value").into())
}

fn print_usage() {
    eprintln!(
        "usage: cargo run --release --features backend-solver,backend-plonky3 --example bench_phase2_sat -- [options]\n\
         --benchmark-root <path>   fixture root\n\
         --fixture <path>          fixture relative path, repeatable\n\
         --runs <n>                repetitions (default: 1)"
    );
}

fn absolutize(path: &Path) -> Result<PathBuf, Box<dyn Error>> {
    if path.is_absolute() {
        Ok(path.to_path_buf())
    } else {
        Ok(env::current_dir()?.join(path))
    }
}

fn elapsed_ms(started: Instant) -> f64 {
    started.elapsed().as_secs_f64() * 1000.0
}

fn median(samples: &[f64]) -> f64 {
    let mut sorted = samples.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
    sorted[sorted.len() / 2]
}
