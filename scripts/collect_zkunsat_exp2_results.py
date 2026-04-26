#!/usr/bin/env python3
import argparse
import csv
import json
from pathlib import Path


def main() -> int:
    args = parse_args()
    rows = []
    with args.manifest.open(newline="") as f:
        for entry in csv.DictReader(f):
            result_path = args.output_dir / "fixtures" / entry["slug"] / "result.json"
            if result_path.exists():
                rows.append(summary_row(json.loads(result_path.read_text())))
            else:
                rows.append({"fixture": entry["label"], "status": "missing"})

    results_dir = args.output_dir / "results"
    results_dir.mkdir(parents=True, exist_ok=True)
    write_csv(results_dir / args.csv_name, rows)
    write_markdown(results_dir / args.md_name, rows)
    print((results_dir / args.md_name).read_text())
    return 0


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--csv-name", default="summary_combined.csv")
    parser.add_argument("--md-name", default="summary_combined.md")
    return parser.parse_args()


def summary_row(result):
    plonky3 = result.get("plonky3") or {}
    zkunsat = result.get("zkunsat") or {}
    return {
        "fixture": result["label"],
        "status": result["status"],
        "vars": result.get("vars"),
        "clauses": result.get("clauses"),
        "steps": result.get("resolution_steps"),
        "width": result.get("max_clause_width"),
        "Plonky3 prove": fmt_ms(plonky3.get("median_prove_ms")),
        "Plonky3 verify": fmt_ms(plonky3.get("median_verify_ms")),
        "Plonky3 proof": fmt_bytes(plonky3.get("proof_bytes")),
        "ZKUNSAT verifier": fmt_ms(zkunsat.get("median_verifier_ms")),
        "ZKUNSAT comm": fmt_bytes(zkunsat.get("median_communication_bytes")),
    }


def fmt_ms(value):
    if value is None:
        return ""
    if value >= 1000:
        return f"{value / 1000:.3f}s"
    return f"{value:.3f}ms"


def fmt_bytes(value):
    if value is None:
        return ""
    if value >= 1024 * 1024 * 1024:
        return f"{value / (1024 * 1024 * 1024):.2f} GiB"
    if value >= 1024 * 1024:
        return f"{value / (1024 * 1024):.2f} MiB"
    if value >= 1024:
        return f"{value / 1024:.2f} KiB"
    return f"{value} B"


FIELDS = [
    "fixture",
    "status",
    "vars",
    "clauses",
    "steps",
    "width",
    "Plonky3 prove",
    "Plonky3 verify",
    "Plonky3 proof",
    "ZKUNSAT verifier",
    "ZKUNSAT comm",
]


def write_csv(path, rows):
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(rows)


def write_markdown(path, rows):
    with path.open("w") as f:
        f.write("| " + " | ".join(FIELDS) + " |\n")
        f.write("| " + " | ".join(["---"] + ["---:"] * (len(FIELDS) - 1)) + " |\n")
        for row in rows:
            f.write("| " + " | ".join(str(row.get(field, "")) for field in FIELDS) + " |\n")


if __name__ == "__main__":
    raise SystemExit(main())
