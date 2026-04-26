#!/usr/bin/env python3
import argparse
import csv
import re
import shutil
import subprocess
import sys
import time
import urllib.request
from pathlib import Path


DEFAULT_REF = "svcomp22"
RAW_BASE = "https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/raw"


def main() -> int:
    args = parse_args()
    root = Path(__file__).resolve().parents[1]
    spec_path = args.spec or root / "benchmarks/zkunsat-exp2/svcomp_instances.csv"
    out_dir = args.output_dir or root / "artifacts/zkunsat-exp2-svcomp"
    generated_manifest = out_dir / "manifest.csv"
    fixtures_dir = out_dir / "fixtures"
    sources_dir = out_dir / "sources"
    results_dir = out_dir / "results"
    picosat = args.picosat or root / ".cache/picosat-965/picosat"
    zkunsat_root = args.zkunsat_root or root.parent / "ZKUNSAT"

    fixtures_dir.mkdir(parents=True, exist_ok=True)
    sources_dir.mkdir(parents=True, exist_ok=True)
    results_dir.mkdir(parents=True, exist_ok=True)

    rows = load_spec(spec_path)
    selected = select_rows(rows, args.fixture, args.max_fixtures)
    manifest_rows = []

    for row in selected:
        slug = row["slug"]
        fixture_dir = fixtures_dir / slug
        fixture_dir.mkdir(parents=True, exist_ok=True)
        print(f"[prepare] {slug}: {row['svcomp_path']} unwind={row['unwind']}", flush=True)
        try:
            source = fetch_svcomp_file(row["svcomp_path"], args.ref, sources_dir)
            fetch_quoted_includes(source, row["svcomp_path"], args.ref, sources_dir)
            formula = fixture_dir / "formula.cnf"
            trace = fixture_dir / "proof.TRACECHECK"
            prf = fixture_dir / "proof.prf"
            unfolded = fixture_dir / "proof.prf.unfold"

            run_cbmc(source, int(row["unwind"]), formula, fixture_dir, args.cbmc)
            if not nontrivial_dimacs(formula):
                raise RuntimeError(f"CBMC produced an empty DIMACS formula: {formula}")
            run_picosat(picosat, formula, trace, fixture_dir)
            convert_trace(zkunsat_root, trace, prf, unfolded)
            stats = unfolded_stats(unfolded)
            manifest_rows.append({
                "slug": slug,
                "label": row["label"],
                "source_path": str(unfolded.resolve()),
                "expected_clauses": str(stats["initial_clauses"]),
                "expected_resolution_steps": str(stats["resolution_steps"]),
                "expected_degree": str(stats["degree"]),
                "zkunsat_reference_s": "",
                "zkunsat_reference_comm_bytes": "",
                "notes": row.get("notes", ""),
            })
            print(
                f"[ok] {slug}: clauses={stats['initial_clauses']} "
                f"steps={stats['resolution_steps']} degree={stats['degree']}",
                flush=True,
            )
        except Exception as exc:
            (fixture_dir / "prepare.failed.txt").write_text(str(exc))
            manifest_rows.append({
                "slug": slug,
                "label": row["label"],
                "source_path": str((fixture_dir / "proof.prf.unfold").resolve()),
                "expected_clauses": "",
                "expected_resolution_steps": "",
                "expected_degree": "",
                "zkunsat_reference_s": "",
                "zkunsat_reference_comm_bytes": "",
                "notes": f"prepare failed: {exc}",
            })
            print(f"[failed] {slug}: {exc}", file=sys.stderr, flush=True)
            if args.fail_fast:
                raise

    write_runner_manifest(generated_manifest, manifest_rows)
    print(f"[manifest] {generated_manifest}")
    print(f"[next] MANIFEST={generated_manifest} scripts/run_zkunsat_exp2.sh")
    return 0


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--spec", type=Path)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--ref", default=DEFAULT_REF)
    parser.add_argument("--fixture", action="append", default=[])
    parser.add_argument("--max-fixtures", type=int)
    parser.add_argument("--cbmc", default="cbmc")
    parser.add_argument("--picosat", type=Path)
    parser.add_argument("--zkunsat-root", type=Path)
    parser.add_argument("--fail-fast", action="store_true")
    return parser.parse_args()


def load_spec(path: Path):
    with path.open(newline="") as f:
        return list(csv.DictReader(f))


def select_rows(rows, fixtures, max_fixtures):
    if fixtures:
        wanted = set(fixtures)
        rows = [row for row in rows if row["slug"] in wanted or row["label"] in wanted]
    if max_fixtures is not None:
        rows = rows[:max_fixtures]
    return rows


def fetch_svcomp_file(svcomp_path: str, ref: str, sources_dir: Path) -> Path:
    target = sources_dir / svcomp_path
    if target.exists():
        return target
    target.parent.mkdir(parents=True, exist_ok=True)
    url = f"{RAW_BASE}/{ref}/{svcomp_path}"
    with urllib.request.urlopen(url, timeout=60) as response:
        target.write_bytes(response.read())
    return target


def fetch_quoted_includes(source: Path, svcomp_path: str, ref: str, sources_dir: Path) -> None:
    queue = [(source, Path(svcomp_path).parent)]
    seen = set()
    while queue:
        local_file, remote_base = queue.pop()
        if local_file in seen or not local_file.exists():
            continue
        seen.add(local_file)
        for include in quoted_includes(local_file.read_text(errors="ignore")):
            remote = (remote_base / include).as_posix()
            local = fetch_svcomp_file(remote, ref, sources_dir)
            queue.append((local, Path(remote).parent))


def quoted_includes(text: str):
    for match in re.finditer(r'^\s*#\s*include\s+"([^"]+)"', text, flags=re.MULTILINE):
        include = match.group(1)
        if not include.startswith("<"):
            yield include


def run_cbmc(source: Path, unwind: int, formula: Path, fixture_dir: Path, cbmc: str) -> None:
    stdout = fixture_dir / "cbmc.stdout"
    stderr = fixture_dir / "cbmc.stderr"
    cmd = [
        cbmc,
        str(source),
        "--unwind",
        str(unwind),
        "--error-label",
        "ERROR",
        "--dimacs",
        "--outfile",
        str(formula),
    ]
    timed_run(cmd, stdout, stderr, allow_codes={0})


def run_picosat(picosat: Path, formula: Path, trace: Path, fixture_dir: Path) -> None:
    stdout = fixture_dir / "picosat.stdout"
    stderr = fixture_dir / "picosat.stderr"
    cmd = [str(picosat), "-T", str(trace), str(formula)]
    timed_run(cmd, stdout, stderr, allow_codes={20})


def convert_trace(zkunsat_root: Path, trace: Path, prf: Path, unfolded: Path) -> None:
    sort_script = zkunsat_root / "prover_backend/Sort.py"
    unfold_script = zkunsat_root / "prover_backend/unfold_proof.py"
    with prf.open("w") as out:
        subprocess.run(["python3", str(sort_script), str(trace)], stdout=out, check=True)
    if unfolded.exists():
        unfolded.unlink()
    subprocess.run(["python3", str(unfold_script), str(prf.resolve())], cwd=zkunsat_root, check=True)


def timed_run(cmd, stdout: Path, stderr: Path, allow_codes) -> None:
    started = time.perf_counter()
    with stdout.open("w") as out, stderr.open("w") as err:
        proc = subprocess.run(cmd, stdout=out, stderr=err)
    elapsed = time.perf_counter() - started
    with stderr.open("a") as err:
        err.write(f"\n[prepare] elapsed_s={elapsed:.6f}\n")
    if proc.returncode not in allow_codes:
        raise RuntimeError(f"{cmd[0]} failed with exit code {proc.returncode}; see {stderr}")


def nontrivial_dimacs(path: Path) -> bool:
    with path.open() as f:
        for line in f:
            if line.startswith("p cnf"):
                parts = line.split()
                return len(parts) >= 4 and int(parts[2]) > 0 and int(parts[3]) > 0
    return False


def unfolded_stats(path: Path):
    initial = 0
    derived = 0
    degree = 0
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith("DEGREE:"):
                degree = int(line.split(":", 1)[1].strip())
                continue
            tokens = line.split()
            if "support:" not in tokens or "pivot:" not in tokens:
                continue
            support = tokens[tokens.index("support:") + 1:tokens.index("pivot:")]
            if support:
                derived += 1
            else:
                initial += 1
    return {"initial_clauses": initial, "resolution_steps": derived, "degree": degree}


def write_runner_manifest(path: Path, rows) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "slug",
        "label",
        "source_path",
        "expected_clauses",
        "expected_resolution_steps",
        "expected_degree",
        "zkunsat_reference_s",
        "zkunsat_reference_comm_bytes",
        "notes",
    ]
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


if __name__ == "__main__":
    raise SystemExit(main())
