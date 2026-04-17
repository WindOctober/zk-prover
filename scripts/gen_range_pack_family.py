#!/usr/bin/env python3

import argparse
from pathlib import Path


HEADER = """// This file is part of the SV-Benchmarks-style collection of verification tasks.
//
// SPDX-License-Identifier: GPL-3.0-or-later

extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() {{ __assert_fail("0", "{name}", 2, "reach_error"); }}

extern int __VERIFIER_nondet_int();

int main() {{
"""


FOOTER = """
    return 0;
}
"""


def render_case(size: int, bound: int) -> str:
    name = f"range_pack_{size}_safe.c"
    lines = [HEADER.format(name=name).rstrip(), ""]

    for idx in range(size):
        lines.append(f"    int a{idx} = __VERIFIER_nondet_int();")
        lines.append(f"    int b{idx} = __VERIFIER_nondet_int();")
        lines.append(f"    int c{idx} = __VERIFIER_nondet_int();")
    lines.append("")

    for idx in range(size):
        lines.append(
            f"    if (a{idx} < 0 || a{idx} > {bound} || b{idx} < 0 || b{idx} > {bound} || c{idx} < 0 || c{idx} > {bound})"
        )
        lines.append("        return 0;")
    lines.append("")

    for idx in range(size):
        lines.append(f"    if (a{idx} > b{idx}) {{")
        lines.append(f"        int sum{idx} = a{idx} + b{idx};")
        lines.append(f"        if (c{idx} <= sum{idx})")
        lines.append("            reach_error();")
        lines.append("    }")
        lines.append("")

    lines.append(FOOTER.strip())
    lines.append("")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate scale-controlled UNSAT range-pack fixtures."
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        required=True,
        help="Directory where generated .c fixtures are written.",
    )
    parser.add_argument(
        "--sizes",
        default="8,16,32,64",
        help="Comma-separated range_pack sizes to generate.",
    )
    parser.add_argument(
        "--bound",
        type=int,
        default=20,
        help="Inclusive upper bound used in the range guards.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    sizes = [int(raw) for raw in args.sizes.split(",") if raw.strip()]
    args.out_dir.mkdir(parents=True, exist_ok=True)

    for size in sizes:
        path = args.out_dir / f"range_pack_{size}_safe.c"
        path.write_text(render_case(size, args.bound), encoding="ascii")
        print(path)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
