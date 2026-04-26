#![cfg(feature = "backend-plonky3")]

use std::{
    env,
    error::Error,
    fs, io,
    net::TcpListener,
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Stdio},
    str::FromStr,
    thread,
    time::{Duration, Instant},
};

use serde::Serialize;
use zk_prover::backend::{
    phase2::resolution_instance_from_unfolded_trace,
    plonky3::air::{
        prove_unsat as prove_plonky3_unsat, prove_unsat_committed as prove_plonky3_unsat_committed,
        verify_unsat as verify_plonky3_unsat,
        verify_unsat_committed as verify_plonky3_unsat_committed,
    },
};

#[derive(Debug, Clone)]
struct Args {
    manifest: PathBuf,
    output_dir: PathBuf,
    runs: usize,
    zkunsat_root: PathBuf,
    zkunsat_bin: Option<PathBuf>,
    zkunsat_threads: usize,
    fixtures: Vec<String>,
    max_fixtures: Option<usize>,
    skip_plonky3: bool,
    skip_zkunsat: bool,
    check_formula_commitment: bool,
}

#[derive(Debug, Clone)]
struct ManifestEntry {
    slug: String,
    label: String,
    source_path: String,
    expected_clauses: Option<usize>,
    expected_resolution_steps: Option<usize>,
    expected_degree: Option<usize>,
    zkunsat_reference_s: Option<f64>,
    zkunsat_reference_comm_bytes: Option<u64>,
    notes: String,
}

#[derive(Debug, Clone, Serialize)]
struct Plonky3Result {
    threads: usize,
    runs: usize,
    prove_samples_ms: Vec<f64>,
    verify_samples_ms: Vec<f64>,
    median_prove_ms: f64,
    median_verify_ms: f64,
    proof_bytes: usize,
}

#[derive(Debug, Clone, Serialize)]
struct ZkunsatResult {
    threads: usize,
    runs: usize,
    wall_samples_ms: Vec<f64>,
    verifier_samples_ms: Vec<f64>,
    communication_samples_bytes: Vec<u64>,
    median_wall_ms: f64,
    median_verifier_ms: f64,
    median_communication_bytes: u64,
}

#[derive(Debug, Clone, Serialize)]
struct FixtureResult {
    slug: String,
    label: String,
    status: String,
    source_path: String,
    resolved_source_path: Option<String>,
    notes: String,
    expected_clauses: Option<usize>,
    expected_resolution_steps: Option<usize>,
    expected_degree: Option<usize>,
    zkunsat_reference_s: Option<f64>,
    zkunsat_reference_comm_bytes: Option<u64>,
    vars: Option<u32>,
    clauses: Option<usize>,
    resolution_steps: Option<usize>,
    max_clause_width: Option<u32>,
    plonky3: Option<Plonky3Result>,
    zkunsat: Option<ZkunsatResult>,
    error: Option<String>,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse()?;
    let manifest_dir = args
        .manifest
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from("."));
    let entries = load_manifest(&args.manifest)?;
    let entries = selected_entries(entries, &args.fixtures, args.max_fixtures);
    let rayon_threads = current_thread_count();

    fs::create_dir_all(args.output_dir.join("fixtures"))?;
    fs::create_dir_all(args.output_dir.join("results"))?;

    println!(
        "manifest={} output_dir={} zkunsat_root={} rayon_threads={} zkunsat_threads={} runs={}",
        args.manifest.display(),
        args.output_dir.display(),
        args.zkunsat_root.display(),
        rayon_threads,
        args.zkunsat_threads,
        args.runs,
    );

    let mut results = Vec::new();
    for entry in entries {
        let fixture_dir = args.output_dir.join("fixtures").join(&entry.slug);
        fs::create_dir_all(&fixture_dir)?;

        let Some(source_path) = resolve_source_path(&manifest_dir, &args.zkunsat_root, &entry)
        else {
            let result = missing_result(entry, "unfolded proof file is not present");
            println!("[MISSING] {} {}", result.slug, result.source_path);
            results.push(result);
            continue;
        };

        println!("[RUN] {} source={}", entry.slug, source_path.display());
        let run_result = run_fixture(&args, &entry, &source_path, &fixture_dir, rayon_threads)
            .unwrap_or_else(|err| failed_result(entry.clone(), &source_path, err.to_string()));
        write_json(fixture_dir.join("result.json"), &run_result)?;
        results.push(run_result);
    }

    write_json(args.output_dir.join("results/summary.json"), &results)?;
    write_summary_csv(args.output_dir.join("results/summary.csv"), &results)?;
    write_summary_markdown(args.output_dir.join("results/summary.md"), &results)?;
    println!("{}", summary_table(&results));

    Ok(())
}

fn run_fixture(
    args: &Args,
    entry: &ManifestEntry,
    source_path: &Path,
    fixture_dir: &Path,
    rayon_threads: usize,
) -> Result<FixtureResult, Box<dyn Error>> {
    let proof_path = materialize_unfolded(source_path, fixture_dir)?.canonicalize()?;
    let unfolded = fs::read_to_string(&proof_path)?;
    let instance = resolution_instance_from_unfolded_trace(&unfolded)?;
    let max_clause_width = instance.max_resolution_clause_width();
    let vars = instance.formula.num_vars;
    let clauses = instance.formula.clauses.len();
    let resolution_steps = instance.proof.steps.len();

    fs::write(
        fixture_dir.join("formula.cnf"),
        instance.formula.to_dimacs(),
    )?;

    let mut errors = Vec::new();
    let plonky3 = if args.skip_plonky3 {
        None
    } else {
        match benchmark_plonky3(
            args.runs,
            &instance,
            fixture_dir,
            rayon_threads,
            args.check_formula_commitment,
        ) {
            Ok(result) => Some(result),
            Err(err) => {
                errors.push(format!("plonky3: {err}"));
                None
            }
        }
    };
    let zkunsat = if args.skip_zkunsat {
        None
    } else {
        match benchmark_zkunsat(
            args.runs,
            &args.zkunsat_root,
            args.zkunsat_bin.as_deref(),
            &proof_path,
            args.zkunsat_threads,
            fixture_dir,
        ) {
            Ok(result) => Some(result),
            Err(err) => {
                errors.push(format!("zkunsat: {err}"));
                None
            }
        }
    };

    Ok(FixtureResult {
        slug: entry.slug.clone(),
        label: entry.label.clone(),
        status: if errors.is_empty() { "ok" } else { "partial" }.to_owned(),
        source_path: entry.source_path.clone(),
        resolved_source_path: Some(source_path.display().to_string()),
        notes: entry.notes.clone(),
        expected_clauses: entry.expected_clauses,
        expected_resolution_steps: entry.expected_resolution_steps,
        expected_degree: entry.expected_degree,
        zkunsat_reference_s: entry.zkunsat_reference_s,
        zkunsat_reference_comm_bytes: entry.zkunsat_reference_comm_bytes,
        vars: Some(vars),
        clauses: Some(clauses),
        resolution_steps: Some(resolution_steps),
        max_clause_width: Some(max_clause_width),
        plonky3,
        zkunsat,
        error: (!errors.is_empty()).then(|| errors.join("; ")),
    })
}

fn benchmark_plonky3(
    runs: usize,
    instance: &zk_prover::backend::phase2::ValidatedResolutionInstance,
    fixture_dir: &Path,
    threads: usize,
    check_formula_commitment: bool,
) -> Result<Plonky3Result, Box<dyn Error>> {
    let mut prove_samples = Vec::with_capacity(runs);
    let mut verify_samples = Vec::with_capacity(runs);
    let mut proof_bytes = 0usize;

    for run in 0..runs {
        let prove_started = Instant::now();
        let proof = if check_formula_commitment {
            prove_plonky3_unsat_committed(instance)?
        } else {
            prove_plonky3_unsat(instance)?
        };
        prove_samples.push(elapsed_ms(prove_started));

        let encoded = postcard::to_allocvec(&proof.proof)?;
        proof_bytes = encoded.len();
        fs::write(
            fixture_dir.join(format!("plonky3_run_{run}.proof.postcard")),
            encoded,
        )?;

        let verify_started = Instant::now();
        if check_formula_commitment {
            verify_plonky3_unsat_committed(&instance.committed_public_statement(), &proof)?;
        } else {
            verify_plonky3_unsat(&instance.public_statement(), &proof)?;
        }
        verify_samples.push(elapsed_ms(verify_started));
    }

    Ok(Plonky3Result {
        threads,
        runs,
        median_prove_ms: median_f64(&prove_samples),
        median_verify_ms: median_f64(&verify_samples),
        prove_samples_ms: prove_samples,
        verify_samples_ms: verify_samples,
        proof_bytes,
    })
}

fn benchmark_zkunsat(
    runs: usize,
    zkunsat_root: &Path,
    zkunsat_bin_override: Option<&Path>,
    proof_path: &Path,
    threads: usize,
    fixture_dir: &Path,
) -> Result<ZkunsatResult, Box<dyn Error>> {
    let binary = zkunsat_bin_override
        .map(PathBuf::from)
        .unwrap_or_else(|| zkunsat_root.join("build/test"));
    let mut wall_samples = Vec::with_capacity(runs);
    let mut verifier_samples = Vec::with_capacity(runs);
    let mut communication_samples = Vec::with_capacity(runs);

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

        let wall_ms = elapsed_ms(started);
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

        let comm1 = parse_communication_bytes(&log1).unwrap_or(0);
        let comm2 = parse_communication_bytes(&log2).unwrap_or(0);
        let verifier_ms = parse_total_seconds(&log2)
            .map(|seconds| seconds * 1000.0)
            .unwrap_or(wall_ms);

        wall_samples.push(wall_ms);
        verifier_samples.push(verifier_ms);
        communication_samples.push(comm1 + comm2);
    }

    Ok(ZkunsatResult {
        threads,
        runs,
        median_wall_ms: median_f64(&wall_samples),
        median_verifier_ms: median_f64(&verifier_samples),
        median_communication_bytes: median_u64(&communication_samples),
        wall_samples_ms: wall_samples,
        verifier_samples_ms: verifier_samples,
        communication_samples_bytes: communication_samples,
    })
}

fn materialize_unfolded(source_path: &Path, fixture_dir: &Path) -> Result<PathBuf, Box<dyn Error>> {
    let proof_path = fixture_dir.join("proof.prf.unfold");
    if source_path.to_string_lossy().ends_with(".gz") {
        let output = fs::File::create(&proof_path)?;
        let status = Command::new("gzip")
            .arg("-dc")
            .arg(source_path)
            .stdout(Stdio::from(output))
            .status()?;
        ensure_success(status, "gzip -dc")?;
    } else {
        fs::copy(source_path, &proof_path)?;
    }
    Ok(proof_path)
}

fn load_manifest(path: &Path) -> Result<Vec<ManifestEntry>, Box<dyn Error>> {
    let raw = fs::read_to_string(path)?;
    let mut entries = Vec::new();
    for (line_index, line) in raw.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') || line.starts_with("slug,") {
            continue;
        }
        let fields = line.splitn(9, ',').collect::<Vec<_>>();
        if fields.len() != 9 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "manifest line {} has {} fields",
                    line_index + 1,
                    fields.len()
                ),
            )
            .into());
        }
        entries.push(ManifestEntry {
            slug: fields[0].trim().to_owned(),
            label: fields[1].trim().to_owned(),
            source_path: fields[2].trim().to_owned(),
            expected_clauses: parse_opt_usize(fields[3])?,
            expected_resolution_steps: parse_opt_usize(fields[4])?,
            expected_degree: parse_opt_usize(fields[5])?,
            zkunsat_reference_s: parse_opt_f64(fields[6])?,
            zkunsat_reference_comm_bytes: parse_opt_u64(fields[7])?,
            notes: fields[8].trim().to_owned(),
        });
    }
    Ok(entries)
}

fn selected_entries(
    entries: Vec<ManifestEntry>,
    fixtures: &[String],
    max_fixtures: Option<usize>,
) -> Vec<ManifestEntry> {
    let mut selected = entries
        .into_iter()
        .filter(|entry| {
            fixtures.is_empty()
                || fixtures
                    .iter()
                    .any(|fixture| fixture == &entry.slug || fixture == &entry.label)
        })
        .collect::<Vec<_>>();
    if let Some(max_fixtures) = max_fixtures {
        selected.truncate(max_fixtures);
    }
    selected
}

fn resolve_source_path(
    manifest_dir: &Path,
    zkunsat_root: &Path,
    entry: &ManifestEntry,
) -> Option<PathBuf> {
    [
        manifest_dir.join(&entry.source_path),
        zkunsat_root.join(&entry.source_path),
        PathBuf::from(&entry.source_path),
    ]
    .into_iter()
    .find(|path| path.exists())
}

fn missing_result(entry: ManifestEntry, reason: &str) -> FixtureResult {
    FixtureResult {
        slug: entry.slug,
        label: entry.label,
        status: "missing".to_owned(),
        source_path: entry.source_path,
        resolved_source_path: None,
        notes: entry.notes,
        expected_clauses: entry.expected_clauses,
        expected_resolution_steps: entry.expected_resolution_steps,
        expected_degree: entry.expected_degree,
        zkunsat_reference_s: entry.zkunsat_reference_s,
        zkunsat_reference_comm_bytes: entry.zkunsat_reference_comm_bytes,
        vars: None,
        clauses: None,
        resolution_steps: None,
        max_clause_width: None,
        plonky3: None,
        zkunsat: None,
        error: Some(reason.to_owned()),
    }
}

fn failed_result(entry: ManifestEntry, source_path: &Path, error: String) -> FixtureResult {
    FixtureResult {
        slug: entry.slug,
        label: entry.label,
        status: "failed".to_owned(),
        source_path: entry.source_path,
        resolved_source_path: Some(source_path.display().to_string()),
        notes: entry.notes,
        expected_clauses: entry.expected_clauses,
        expected_resolution_steps: entry.expected_resolution_steps,
        expected_degree: entry.expected_degree,
        zkunsat_reference_s: entry.zkunsat_reference_s,
        zkunsat_reference_comm_bytes: entry.zkunsat_reference_comm_bytes,
        vars: None,
        clauses: None,
        resolution_steps: None,
        max_clause_width: None,
        plonky3: None,
        zkunsat: None,
        error: Some(error),
    }
}

fn write_summary_csv(path: PathBuf, rows: &[FixtureResult]) -> Result<(), Box<dyn Error>> {
    let mut out = String::from(
        "slug,label,status,vars,clauses,resolution_steps,max_clause_width,expected_clauses,expected_resolution_steps,expected_degree,plonky3_prove_ms,plonky3_verify_ms,plonky3_proof_bytes,zkunsat_verifier_ms,zkunsat_wall_ms,zkunsat_comm_bytes,zkunsat_reference_s,zkunsat_reference_comm_bytes,error\n",
    );
    for row in rows {
        out.push_str(&format!(
            "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}\n",
            row.slug,
            row.label,
            row.status,
            fmt_opt(row.vars),
            fmt_opt(row.clauses),
            fmt_opt(row.resolution_steps),
            fmt_opt(row.max_clause_width),
            fmt_opt(row.expected_clauses),
            fmt_opt(row.expected_resolution_steps),
            fmt_opt(row.expected_degree),
            row.plonky3
                .as_ref()
                .map(|value| format!("{:.3}", value.median_prove_ms))
                .unwrap_or_default(),
            row.plonky3
                .as_ref()
                .map(|value| format!("{:.3}", value.median_verify_ms))
                .unwrap_or_default(),
            row.plonky3
                .as_ref()
                .map(|value| value.proof_bytes.to_string())
                .unwrap_or_default(),
            row.zkunsat
                .as_ref()
                .map(|value| format!("{:.3}", value.median_verifier_ms))
                .unwrap_or_default(),
            row.zkunsat
                .as_ref()
                .map(|value| format!("{:.3}", value.median_wall_ms))
                .unwrap_or_default(),
            row.zkunsat
                .as_ref()
                .map(|value| value.median_communication_bytes.to_string())
                .unwrap_or_default(),
            row.zkunsat_reference_s
                .map(|value| format!("{value:.6}"))
                .unwrap_or_default(),
            fmt_opt(row.zkunsat_reference_comm_bytes),
            row.error.clone().unwrap_or_default().replace(',', ";"),
        ));
    }
    fs::write(path, out)?;
    Ok(())
}

fn write_summary_markdown(path: PathBuf, rows: &[FixtureResult]) -> Result<(), Box<dyn Error>> {
    fs::write(path, summary_table(rows))?;
    Ok(())
}

fn summary_table(rows: &[FixtureResult]) -> String {
    let mut out = String::from(
        "| fixture | status | vars | clauses | steps | width | Plonky3 prove | Plonky3 verify | Plonky3 proof | ZKUNSAT verifier | ZKUNSAT comm |\n",
    );
    out.push_str("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n");
    for row in rows {
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |\n",
            row.label,
            row.status,
            fmt_opt(row.vars),
            fmt_opt(row.clauses.or(row.expected_clauses)),
            fmt_opt(row.resolution_steps.or(row.expected_resolution_steps)),
            fmt_opt(
                row.max_clause_width
                    .or(row.expected_degree.map(|value| value as u32))
            ),
            row.plonky3
                .as_ref()
                .map(|value| human_time_ms(value.median_prove_ms))
                .unwrap_or_else(|| "-".to_owned()),
            row.plonky3
                .as_ref()
                .map(|value| human_time_ms(value.median_verify_ms))
                .unwrap_or_else(|| "-".to_owned()),
            row.plonky3
                .as_ref()
                .map(|value| human_bytes(value.proof_bytes as u64))
                .unwrap_or_else(|| "-".to_owned()),
            row.zkunsat
                .as_ref()
                .map(|value| human_time_ms(value.median_verifier_ms))
                .unwrap_or_else(|| {
                    row.zkunsat_reference_s
                        .map(|seconds| format!("{} ref", human_time_ms(seconds * 1000.0)))
                        .unwrap_or_else(|| "-".to_owned())
                }),
            row.zkunsat
                .as_ref()
                .map(|value| human_bytes(value.median_communication_bytes))
                .unwrap_or_else(|| {
                    row.zkunsat_reference_comm_bytes
                        .map(|bytes| format!("{} ref", human_bytes(bytes)))
                        .unwrap_or_else(|| "-".to_owned())
                }),
        ));
    }
    out
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

fn parse_communication_bytes(log: &str) -> Option<u64> {
    log.lines()
        .rev()
        .find_map(|line| line.trim().strip_prefix("communication:")?.parse().ok())
}

fn parse_total_seconds(log: &str) -> Option<f64> {
    log.lines().rev().find_map(|line| {
        let tokens = line.split_whitespace().collect::<Vec<_>>();
        tokens
            .windows(2)
            .find(|pair| pair[0] == "t")
            .and_then(|pair| pair[1].parse::<f64>().ok())
    })
}

fn parse_opt_usize(raw: &str) -> Result<Option<usize>, Box<dyn Error>> {
    parse_opt(raw)
}

fn parse_opt_u64(raw: &str) -> Result<Option<u64>, Box<dyn Error>> {
    parse_opt(raw)
}

fn parse_opt_f64(raw: &str) -> Result<Option<f64>, Box<dyn Error>> {
    parse_opt(raw)
}

fn parse_opt<T>(raw: &str) -> Result<Option<T>, Box<dyn Error>>
where
    T: FromStr,
    T::Err: Error + 'static,
{
    let raw = raw.trim();
    if raw.is_empty() {
        Ok(None)
    } else {
        raw.parse::<T>()
            .map(Some)
            .map_err(|err| Box::new(err) as Box<dyn Error>)
    }
}

fn fmt_opt(value: Option<impl ToString>) -> String {
    value.map(|value| value.to_string()).unwrap_or_default()
}

fn human_time_ms(ms: f64) -> String {
    if ms >= 1000.0 {
        format!("{:.3}s", ms / 1000.0)
    } else {
        format!("{ms:.3}ms")
    }
}

fn human_bytes(bytes: u64) -> String {
    const KIB: f64 = 1024.0;
    const MIB: f64 = 1024.0 * 1024.0;
    const GIB: f64 = 1024.0 * 1024.0 * 1024.0;
    let bytes_f = bytes as f64;
    if bytes_f >= GIB {
        format!("{:.2} GiB", bytes_f / GIB)
    } else if bytes_f >= MIB {
        format!("{:.2} MiB", bytes_f / MIB)
    } else if bytes_f >= KIB {
        format!("{:.2} KiB", bytes_f / KIB)
    } else {
        format!("{bytes} B")
    }
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

fn median_f64(samples: &[f64]) -> f64 {
    let mut sorted = samples.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
    sorted[sorted.len() / 2]
}

fn median_u64(samples: &[u64]) -> u64 {
    let mut sorted = samples.to_vec();
    sorted.sort_unstable();
    sorted[sorted.len() / 2]
}

fn elapsed_ms(started: Instant) -> f64 {
    started.elapsed().as_secs_f64() * 1000.0
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

impl Args {
    fn parse() -> Result<Self, Box<dyn Error>> {
        let cwd = env::current_dir()?;
        let workspace_root = cwd
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| PathBuf::from(".."));
        let mut args = env::args().skip(1);
        let mut parsed = Self {
            manifest: cwd.join("benchmarks/zkunsat-exp2/manifest.csv"),
            output_dir: cwd.join("artifacts/zkunsat-exp2"),
            runs: 1,
            zkunsat_root: env::var_os("ZKUNSAT_ROOT")
                .map(PathBuf::from)
                .unwrap_or_else(|| workspace_root.join("ZKUNSAT")),
            zkunsat_bin: env::var_os("ZKUNSAT_BIN").map(PathBuf::from),
            zkunsat_threads: env::var("ZKUNSAT_THREADS")
                .ok()
                .and_then(|value| value.parse().ok())
                .unwrap_or_else(current_thread_count),
            fixtures: Vec::new(),
            max_fixtures: None,
            skip_plonky3: false,
            skip_zkunsat: false,
            check_formula_commitment: false,
        };

        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--manifest" => parsed.manifest = PathBuf::from(required_value(&mut args, &arg)?),
                "--output-dir" => {
                    parsed.output_dir = PathBuf::from(required_value(&mut args, &arg)?)
                }
                "--runs" => parsed.runs = required_value(&mut args, &arg)?.parse()?,
                "--zkunsat-root" => {
                    parsed.zkunsat_root = PathBuf::from(required_value(&mut args, &arg)?)
                }
                "--zkunsat-bin" => {
                    parsed.zkunsat_bin = Some(PathBuf::from(required_value(&mut args, &arg)?))
                }
                "--zkunsat-threads" => {
                    parsed.zkunsat_threads = required_value(&mut args, &arg)?.parse()?
                }
                "--fixture" => parsed.fixtures.push(required_value(&mut args, &arg)?),
                "--max-fixtures" => {
                    parsed.max_fixtures = Some(required_value(&mut args, &arg)?.parse()?)
                }
                "--skip-plonky3" => parsed.skip_plonky3 = true,
                "--skip-zkunsat" => parsed.skip_zkunsat = true,
                "--check-formula-commitment" => parsed.check_formula_commitment = true,
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

        if parsed.runs == 0 {
            return Err(
                io::Error::new(io::ErrorKind::InvalidInput, "--runs must be positive").into(),
            );
        }
        Ok(parsed)
    }
}

fn required_value(
    args: &mut impl Iterator<Item = String>,
    flag: &str,
) -> Result<String, Box<dyn Error>> {
    args.next().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("{flag} requires a value"),
        )
        .into()
    })
}

fn print_usage() {
    eprintln!(
        "usage: cargo run --release --features backend-plonky3 --example bench_zkunsat_exp2 -- [options]\n\
         options:\n\
         --manifest <path>         manifest CSV (default: benchmarks/zkunsat-exp2/manifest.csv)\n\
         --output-dir <path>       output directory (default: artifacts/zkunsat-exp2)\n\
         --runs <n>                repetitions per backend (default: 1)\n\
         --zkunsat-root <path>     local ZKUNSAT checkout (default: ../ZKUNSAT)\n\
         --zkunsat-bin <path>      ZKUNSAT binary (default: <zkunsat-root>/build/test)\n\
         --zkunsat-threads <n>     ZKUNSAT thread count (default: ZKUNSAT_THREADS or Rayon threads)\n\
         --fixture <slug>          run one manifest slug/label; can be repeated\n\
         --max-fixtures <n>        run only the first n selected rows\n\
         --skip-plonky3            do not run the Plonky3 backend\n\
         --skip-zkunsat            do not run ZKUNSAT\n\
         --check-formula-commitment enable Plonky3 private-formula commitment constraints"
    );
}
