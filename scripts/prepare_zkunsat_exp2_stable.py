#!/usr/bin/env python3
import argparse
import csv
import gzip
import zipfile
from pathlib import Path


def main() -> int:
    args = parse_args()
    root = Path(__file__).resolve().parents[1]
    spec = args.spec or root / "benchmarks/zkunsat-exp2/stable_artifact_instances.csv"
    out_dir = args.output_dir or root / "artifacts/zkunsat-exp2-stable"
    zkunsat_root = args.zkunsat_root or root.parent / "ZKUNSAT"
    zip_path = args.zip or zkunsat_root / "ZKUNSAT_STABLE.zip"

    fixtures_dir = out_dir / "fixtures"
    fixtures_dir.mkdir(parents=True, exist_ok=True)
    rows = []

    with zipfile.ZipFile(zip_path) as archive:
        for row in load_spec(spec):
            slug = row["slug"]
            member = row["zip_member"]
            fixture_dir = fixtures_dir / slug
            fixture_dir.mkdir(parents=True, exist_ok=True)
            unfolded = fixture_dir / "proof.prf.unfold"

            print(f"[extract] {slug}: {member}", flush=True)
            data = archive.read(member)
            if member.endswith(".gz"):
                data = gzip.decompress(data)
            unfolded.write_bytes(data)
            stats = unfolded_stats(unfolded)
            rows.append({
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
                f"steps={stats['resolution_steps']} degree={stats['degree']} "
                f"width={stats['max_width']}",
                flush=True,
            )

    write_runner_manifest(out_dir / "manifest.csv", rows)
    print(f"[manifest] {out_dir / 'manifest.csv'}")
    return 0


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--spec", type=Path)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--zkunsat-root", type=Path)
    parser.add_argument("--zip", type=Path)
    return parser.parse_args()


def load_spec(path: Path):
    with path.open(newline="") as f:
        return list(csv.DictReader(f))


def unfolded_stats(path: Path):
    initial = 0
    derived = 0
    degree = 0
    max_width = 0
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith("DEGREE:"):
                degree = int(line.split(":", 1)[1].strip())
                continue
            tokens = line.split()
            if "clause:" not in tokens or "support:" not in tokens or "pivot:" not in tokens:
                continue
            clause = tokens[tokens.index("clause:") + 1:tokens.index("support:")]
            support = tokens[tokens.index("support:") + 1:tokens.index("pivot:")]
            if support:
                derived += 1
            else:
                initial += 1
            max_width = max(max_width, len(clause))
    return {
        "initial_clauses": initial,
        "resolution_steps": derived,
        "degree": degree,
        "max_width": max_width,
    }


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
