#!/usr/bin/env python3
import argparse
from pathlib import Path

import matplotlib.colors as mcolors
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd


SYSTEMS = ["ZK-ProVer", "ZKUNSAT"]
WIDTH_BUCKETS = np.array([16, 32, 64, 96, 128, 192, 256], dtype=float)
STEP_BUCKETS = np.array([100, 500, 1000, 2000, 5000, 10000, 20000], dtype=float)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data-dir", type=Path, default=Path("Data"))
    parser.add_argument("--fig-dir", type=Path, default=Path("Figures"))
    args = parser.parse_args()

    memory = pd.read_csv(args.data_dir / "rq2_memory.csv")
    stress = pd.read_csv(args.data_dir / "rq2_memory_stress.csv")
    measurements = pd.concat([memory, stress], ignore_index=True)

    grids = {}
    for system in SYSTEMS:
        system_data = measurements[measurements["system"] == system].copy()
        if system == "ZK-ProVer":
            # The tiny nan instance is an outlier whose backend does not allocate
            # the same wide UNSAT trace; exclude it from the scaling fit.
            system_data = system_data[system_data["max_rss_gib"] > 0.5]
        coeffs = fit_log_model(system_data)
        grids[system] = estimate_grid(coeffs)

    cmap = mcolors.LinearSegmentedColormap.from_list(
        "paper_bluegray",
        ["#e9eef4", "#dce7f2", "#c5d7ea", "#9fbeda", "#739bc6", "#496fa9", "#25346f"],
    )

    args.fig_dir.mkdir(parents=True, exist_ok=True)
    fig, axes = plt.subplots(1, 2, figsize=(7.15, 2.65), constrained_layout=True)
    shared_norm = mcolors.Normalize(
        vmin=min(float(grid.min()) for grid in grids.values()),
        vmax=max(float(grid.max()) for grid in grids.values()),
    )

    last_image = None
    for ax, system in zip(axes, SYSTEMS):
        grid = grids[system]
        last_image = ax.imshow(grid, cmap=cmap, norm=shared_norm, origin="lower", aspect="auto")
        annotate_cells(ax, grid, shared_norm)
        style_axis(ax, system)

    cbar = fig.colorbar(last_image, ax=axes, fraction=0.035, pad=0.018)
    cbar.ax.tick_params(labelsize=6.6)
    cbar.set_label("peak RSS (GiB)", fontsize=7.2)

    for ext in ("pdf", "png"):
        output = args.fig_dir / f"rq2-memory-heatmap.{ext}"
        fig.savefig(output, dpi=300)
        print(f"wrote {output}")
    return 0


def fit_log_model(data: pd.DataFrame) -> np.ndarray:
    x = np.column_stack(
        [
            np.ones(len(data)),
            np.log(data["steps"].to_numpy(dtype=float)),
            np.log(data["width"].to_numpy(dtype=float)),
        ]
    )
    y = np.log(data["max_rss_gib"].to_numpy(dtype=float))
    return np.linalg.lstsq(x, y, rcond=None)[0]


def estimate_grid(coeffs: np.ndarray) -> np.ndarray:
    steps, widths = np.meshgrid(STEP_BUCKETS, WIDTH_BUCKETS, indexing="ij")
    log_values = coeffs[0] + coeffs[1] * np.log(steps) + coeffs[2] * np.log(widths)
    return np.exp(log_values)


def annotate_cells(ax, grid: np.ndarray, norm: mcolors.Normalize) -> None:
    for row in range(grid.shape[0]):
        for col in range(grid.shape[1]):
            value = grid[row, col]
            color = "white" if norm(value) > 0.62 else "#142d44"
            ax.text(
                col,
                row,
                f"{value:.1f}",
                ha="center",
                va="center",
                fontsize=5.9,
                color=color,
            )


def style_axis(ax, title: str) -> None:
    ax.set_title(title, fontsize=8.4, pad=4)
    ax.set_xticks(range(len(WIDTH_BUCKETS)))
    ax.set_xticklabels([str(int(w)) for w in WIDTH_BUCKETS], fontsize=6.6)
    ax.set_yticks(range(len(STEP_BUCKETS)))
    ax.set_yticklabels([format_steps(int(s)) for s in STEP_BUCKETS], fontsize=6.6)
    ax.set_xlabel("maximum clause width", fontsize=7.2)
    ax.set_ylabel("resolution steps", fontsize=7.2)
    ax.set_xticks(np.arange(-0.5, len(WIDTH_BUCKETS), 1), minor=True)
    ax.set_yticks(np.arange(-0.5, len(STEP_BUCKETS), 1), minor=True)
    ax.grid(which="minor", color="white", linestyle="-", linewidth=0.85)
    ax.tick_params(which="minor", bottom=False, left=False)
    ax.tick_params(axis="both", length=0)
    for spine in ax.spines.values():
        spine.set_visible(False)


def format_steps(value: int) -> str:
    if value >= 1000:
        return f"{value // 1000}k" if value % 1000 == 0 else f"{value / 1000:.1f}k"
    return str(value)


if __name__ == "__main__":
    raise SystemExit(main())
