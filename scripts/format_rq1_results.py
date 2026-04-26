#!/usr/bin/env python3
"""Collect RQ1 benchmark CSVs into paper-ready summary files."""

from __future__ import annotations

import argparse
import csv
import statistics
from pathlib import Path


FIXTURES = [
    ("vendor/sv-benchmarks/c/validation-crafted/if.c", "if.c", "SAT"),
    ("vendor/sv-benchmarks/c/validation-crafted/ternary.c", "ternary.c", "SAT"),
    ("synthetic-c/validation-crafted/diamond_safe.c", "diamond_safe.c", "UNSAT"),
    ("synthetic-c/validation-crafted/range_arith_safe.c", "range_arith_safe.c", "UNSAT"),
    ("synthetic-c/validation-crafted/branch_sum_safe.c", "branch_sum_safe.c", "UNSAT"),
    ("synthetic-c/validation-crafted/nested_guard_safe.c", "nested_guard_safe.c", "UNSAT"),
    ("synthetic-c/validation-crafted/range_pack_2_safe.c", "range_pack_2_safe.c", "UNSAT"),
    ("svcomp-unrolled/loop-invgen/down_3_unrolled.c", "down_3_unrolled.c", "UNSAT"),
    (
        "svcomp-unrolled/loop-invgen/large_const_2_unrolled.c",
        "large_const_2_unrolled.c",
        "UNSAT",
    ),
    (
        "svcomp-unrolled/loop-lit/bhmr2007_3_bug_unrolled.c",
        "bhmr2007_3_bug_unrolled.c",
        "SAT",
    ),
]

FIXTURE_SET = {fixture for fixture, _, _ in FIXTURES}


def main() -> None:
    args = parse_args()
    out_dir = args.out_dir
    results_dir = out_dir / "results"
    results_dir.mkdir(parents=True, exist_ok=True)

    p1 = {}
    for path in [
        out_dir / "phase1_official.csv",
        out_dir / "phase1_synthetic.csv",
        out_dir / "phase1_unrolled.csv",
    ]:
        p1.update(load_phase1(path))

    p2 = {}
    for path in [
        out_dir / "phase2_sat_official.csv",
        out_dir / "phase2_sat_unrolled.csv",
    ]:
        p2.update(load_phase2_sat(path))
    for path in [
        out_dir / "phase2_synthetic" / "results" / f"summary_threads_{args.threads}.csv",
        out_dir / "phase2_unrolled" / "results" / f"summary_threads_{args.threads}.csv",
    ]:
        p2.update(load_phase2_unsat(path))

    summary_rows = []
    for fixture, label, branch in FIXTURES:
        summary_rows.append(
            {
                "fixture": fixture,
                "label": label,
                "branch": branch,
                "p1_prove_s": maybe_float(p1.get(fixture, {}).get("prove_ms"), scale=1000.0),
                "p1_verify_ms": maybe_float(p1.get(fixture, {}).get("verify_ms")),
                "p1_proof_kib": maybe_float(p1.get(fixture, {}).get("proof_bytes"), scale=1024.0),
                "p2_prove_s": maybe_float(p2.get(fixture, {}).get("prove_ms"), scale=1000.0),
                "p2_verify_ms": maybe_float(p2.get(fixture, {}).get("verify_ms")),
                "p2_proof_kib": maybe_float(p2.get(fixture, {}).get("proof_bytes"), scale=1024.0),
            }
        )

    write_summary_csv(results_dir / "rq1_summary.csv", summary_rows)
    write_latex_table(results_dir / "rq1_table.tex", summary_rows)
    print(f"wrote {results_dir / 'rq1_summary.csv'}")
    print(f"wrote {results_dir / 'rq1_table.tex'}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--threads", type=int, required=True)
    return parser.parse_args()


def load_phase1(path: Path) -> dict[str, dict[str, float]]:
    rows = list(csv_rows(path))
    grouped: dict[str, list[dict[str, str]]] = {}
    for row in rows:
        if row.get("fixture") in FIXTURE_SET:
            grouped.setdefault(row["fixture"], []).append(row)

    out = {}
    for fixture, fixture_rows in grouped.items():
        out[fixture] = {
            "prove_ms": median_float(fixture_rows, "prove_ms"),
            "verify_ms": median_float(fixture_rows, "verify_ms"),
            "proof_bytes": first_positive_float(fixture_rows, "proof_bytes"),
        }
    return out


def load_phase2_sat(path: Path) -> dict[str, dict[str, float]]:
    out = {}
    for row in csv_rows(path):
        fixture = row.get("fixture")
        if fixture in FIXTURE_SET and row.get("status") == "SAT":
            out[fixture] = {
                "prove_ms": parse_float(row.get("median_prove_ms")),
                "verify_ms": parse_float(row.get("median_verify_ms")),
                "proof_bytes": parse_float(row.get("proof_bytes")),
            }
    return out


def load_phase2_unsat(path: Path) -> dict[str, dict[str, float]]:
    out = {}
    for row in csv_rows(path):
        fixture = row.get("fixture")
        if fixture in FIXTURE_SET and row.get("backend") == "plonky3":
            out[fixture] = {
                "prove_ms": parse_float(row.get("median_prove_ms")),
                "verify_ms": parse_float(row.get("median_verify_ms")),
                "proof_bytes": parse_float(row.get("proof_bytes")),
            }
    return out


def csv_rows(path: Path) -> list[dict[str, str]]:
    if not path.exists():
        return []
    lines = [line.strip() for line in path.read_text().splitlines() if line.strip()]
    header_index = next((i for i, line in enumerate(lines) if line.startswith("fixture,")), None)
    if header_index is None:
        return []
    header = lines[header_index]
    rows = []
    for line in lines[header_index + 1 :]:
        if not any(line.startswith(f"{fixture},") for fixture in FIXTURE_SET):
            continue
        parsed = next(csv.DictReader([header, line]))
        rows.append(parsed)
    return rows


def median_float(rows: list[dict[str, str]], key: str) -> float | None:
    values = [parse_float(row.get(key)) for row in rows]
    values = [value for value in values if value is not None and value > 0]
    if not values:
        return None
    return statistics.median(values)


def first_positive_float(rows: list[dict[str, str]], key: str) -> float | None:
    for row in rows:
        value = parse_float(row.get(key))
        if value is not None and value > 0:
            return value
    return None


def parse_float(value: str | None) -> float | None:
    if value is None or value == "":
        return None
    try:
        return float(value)
    except ValueError:
        return None


def maybe_float(value: float | None, scale: float = 1.0) -> float | None:
    if value is None:
        return None
    return value / scale


def write_summary_csv(path: Path, rows: list[dict[str, object]]) -> None:
    fields = [
        "fixture",
        "branch",
        "p1_prove_s",
        "p1_verify_ms",
        "p1_proof_kib",
        "p2_prove_s",
        "p2_verify_ms",
        "p2_proof_kib",
    ]
    with path.open("w", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    field: fmt_csv(row[field]) if field not in {"fixture", "branch"} else row[field]
                    for field in fields
                }
            )


def write_latex_table(path: Path, rows: list[dict[str, object]]) -> None:
    lines = [
        "% Generated by scripts/format_rq1_results.py.",
        "% Cell format: prove(s) / verify(ms) / proof(KiB).",
        "\\begin{table}[t]",
        "\\centering",
        "\\small",
        "\\caption{End-to-end RQ1 proving and verification cost.}",
        "\\label{tab:rq1-proof-cost}",
        "\\begin{tabular}{llcc}",
        "\\toprule",
        "Fixture & Branch & P1: SP1 & P2: Plonky3 \\\\",
        "\\midrule",
    ]
    for row in rows:
        lines.append(
            "{} & {} & {} & {} \\\\".format(
                latex_texttt(str(row["label"])),
                row["branch"],
                fmt_cell(
                    row["p1_prove_s"],
                    row["p1_verify_ms"],
                    row["p1_proof_kib"],
                ),
                fmt_cell(
                    row["p2_prove_s"],
                    row["p2_verify_ms"],
                    row["p2_proof_kib"],
                ),
            )
        )
    lines.extend(
        [
            "\\bottomrule",
            "\\end{tabular}",
            "\\end{table}",
            "",
        ]
    )
    path.write_text("\n".join(lines))


def fmt_csv(value: object) -> str:
    if value is None:
        return ""
    return f"{float(value):.3f}"


def fmt_cell(prove_s: object, verify_ms: object, proof_kib: object) -> str:
    if prove_s is None or verify_ms is None or proof_kib is None:
        return "--"
    return "{} / {:.1f} / {:.1f}".format(fmt_seconds(float(prove_s)), float(verify_ms), float(proof_kib))


def fmt_seconds(value: float) -> str:
    if value >= 100:
        return f"{value:.1f}"
    if value >= 10:
        return f"{value:.2f}"
    return f"{value:.2f}"


def latex_texttt(value: str) -> str:
    escaped = value.replace("\\", "\\textbackslash{}").replace("_", "\\_")
    return f"\\texttt{{{escaped}}}"


if __name__ == "__main__":
    main()
