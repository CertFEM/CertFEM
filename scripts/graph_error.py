#!/usr/bin/env python3

import argparse
import os
import xml.etree.ElementTree as ET
from pathlib import Path
import base64
import types

import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter
import meshio
import numpy as np
from meshio.vtu import _vtu


# Monkey-patch base64 stdlib to fix Python breaking change
def legacy_b64decode(data):
    pad = b"=" if isinstance(data, bytes) else "="
    return base64.b64decode(data.split(pad, 1)[0] + pad * 2)

_vtu.base64 = types.SimpleNamespace(
    b64decode=legacy_b64decode,
    b64encode=base64.b64encode,
)


def read_vtu(path):
    path = Path(path)

    data = path.read_bytes()
    path.write_bytes(data.replace(b'version="2.2"', b'version="1.0"', 1))

    print(f"Reading {path}")
    return meshio.read(path)


def l2_error(mesh, diff):
    total = 0.0

    # Get triangle vertex indices from the VTU.
    triangles = mesh.cells_dict["triangle"]

    for triangle in triangles:
        i, j, k = triangle

        p0 = mesh.points[i][:2]
        p1 = mesh.points[j][:2]
        p2 = mesh.points[k][:2]

        # Physical area of this triangle.
        area = 0.5 * abs(np.cross(p1 - p0, p2 - p0))

        e0 = diff[i]
        e1 = diff[j]
        e2 = diff[k]

        # Exact integral of e(x)^2 over a P1 triangle.
        total += area / 6.0 * (
            e0*e0 + e1*e1 + e2*e2
            + e0*e1 + e0*e2 + e1*e2
        )

    return np.sqrt(total)


def h1_error(mesh, diff):
    """Compute the H1 error between two P1 solutions.

    `diff[i]` is the difference between the two solutions at vertex i.
    The entries of `diff` must correspond to the point ordering in `mesh`.
    """

    l2_squared = 0.0
    grad_squared = 0.0

    triangles = mesh.cells_dict["triangle"]

    for triangle in triangles:
        i, j, k = triangle

        # Triangle coordinates.
        p0 = mesh.points[i][:2]
        p1 = mesh.points[j][:2]
        p2 = mesh.points[k][:2]

        # Error values at the three vertices.
        e0 = diff[i]
        e1 = diff[j]
        e2 = diff[k]

        # Matrix mapping the reference triangle onto this triangle.
        B = np.column_stack((p1 - p0, p2 - p0))

        area = 0.5 * abs(np.linalg.det(B))

        #
        # L2 part:
        #
        # Exact integral of e(x)^2 over a triangle when e is P1.
        #
        l2_squared += area / 6.0 * (
            e0*e0 + e1*e1 + e2*e2
            + e0*e1 + e0*e2 + e1*e2
        )

        #
        # Gradient part:
        #
        # Because a P1 function is linear on each triangle, its gradient
        # is constant over the entire triangle.
        #
        grad = np.linalg.solve(
            B.T,
            np.array([e1 - e0, e2 - e0])
        )

        grad_squared += area * np.dot(grad, grad)

    h1_seminorm = np.sqrt(grad_squared)
    h1_norm = np.sqrt(l2_squared + grad_squared)

    return h1_norm, h1_seminorm


def _plot(problems, output=None):
    fig, axes = plt.subplots(
        1,
        len(problems),
        figsize=(5 * len(problems), 4),
        sharey=True
    )

    if len(problems) == 1:
        axes = [axes]

    percent_values = [
        comparison[3]
        for _, comparisons in problems
        for comparison in comparisons]

    percent_min = min(percent_values)
    percent_max = max(percent_values)

    for i, (ax, (problem, comparisons)) in enumerate(zip(axes, problems)):
        # Right-hand axis for relative error.
        ax_percent = ax.twinx()
        ax.set_yscale("log")
        ax_percent.set_yscale("log")
        ax_percent.set_ylim(percent_min / 2, percent_max * 2)

        if i != len(problems) - 1:
            # ax_percent.spines["right"].set_visible(False)
            ax_percent.set_yticks([])
        else:
            # ax_percent.spines["right"].set_visible(True)
            ax_percent.yaxis.tick_right()
            ax_percent.yaxis.set_label_position("right")
            ax_percent.set_ylabel("Relative difference")

        x = np.arange(3)
        width = 0.8 / len(comparisons)
        start = -(len(comparisons) - 1) * width / 2

        for i, (label, max_error, mean_error, relative_error) in enumerate(comparisons):
            offset = start + i * width

            # One call so max and mean use the same color.
            bars = ax.bar(
                x[:2] + offset,
                [max_error, mean_error],
                width,
                label=label,
            )

            # Relative-max bar uses the same color on the percent axis.
            ax_percent.bar(
                x[2] + offset,
                relative_error,
                width,
                color=bars[0].get_facecolor(),
            )

        ax.set_title(problem)

        ax.set_xticks(x)
        ax.set_xticklabels([
            "Absolute max",
            "Absolute mean",
            "Relative max",
        ])

        # ax.yaxis.set_major_formatter(FormatStrFormatter("%.2g"))
        # ax_percent.yaxis.set_major_formatter(FormatStrFormatter("%.2g"))

    # Shared axis labels and legend
    axes[0].set_ylabel("Absolute error")
    handles, labels = axes[0].get_legend_handles_labels()
    sci = FuncFormatter(lambda y, _: f"{y:.0E}")
    ax.yaxis.set_major_formatter(sci)
    ax_percent.yaxis.set_major_formatter(sci)

    fig.legend( handles, labels, loc="lower center")
    fig.subplots_adjust(bottom=0.25, wspace=0.05)

    plt.show()
    if output is not None:
        fig.savefig(output, dpi=300, bbox_inches="tight")


def _get_stats(a, b, field):
    ua = a.point_data[field].flatten()
    ub = b.point_data[field].flatten()

    tol = 1e-12

    # Sort B by its first coordinate.
    order = np.argsort(b.points[:, 0])
    sorted_x = b.points[order, 0]

    # Find candidate ranges for all points in A.
    lo = np.searchsorted(sorted_x, a.points[:, 0] - tol, side="left")
    hi = np.searchsorted(sorted_x, a.points[:, 0] + tol, side="right")

    used_b = np.zeros(len(b.points), dtype=bool)
    matched_b = np.empty(len(a.points), dtype=int)

    for i, point_a in enumerate(a.points):
        candidates = order[lo[i]:hi[i]]

        matches = candidates[
            np.all(
                np.isclose(b.points[candidates], point_a, atol=tol, rtol=0),
                axis=1
            )
        ]

        if len(matches) == 0:
            raise RuntimeError(f"No matching point in B for {point_a}")

        if len(matches) > 1:
            raise RuntimeError(f"Multiple matching points in B for {point_a}")

        j = matches[0]
        if used_b[j]:
            raise RuntimeError(f"B[{j}] was matched more than once")

        used_b[j] = True
        matched_b[i] = j

    if not np.all(used_b):
        missing = np.where(~used_b)[0]
        raise RuntimeError(f"Unmatched points in B: {missing}")

    diff = ua - ub[matched_b]

    max_a = np.max(np.abs(ua))
    max_b = np.max(np.abs(ub))
    max_value = max(max_a, max_b)
    max_abs_diff = np.max(np.abs(diff))
    mean_abs_diff = np.mean(np.abs(diff))
    # NOTE: this is no longer percent, now it's just relative
    max_percent_diff = max_abs_diff / max_value

    print("max abs difference:", max_abs_diff)
    print("mean abs difference:", mean_abs_diff)
    print(f"max relative difference: {max_percent_diff}")

    return max_abs_diff, mean_abs_diff, max_percent_diff


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--problem",
        action="append",
        nargs="+",
        required=True,
        help="Problem name followed by 2 or 3 VTU files")
    parser.add_argument("--field", default="u")
    parser.add_argument(
        "--labels",
        nargs="+",
        default=["A", "B", "C"],
    )
    parser.add_argument("--output", default="error.png")
    args = parser.parse_args()

    problems = []
    for problem_args in args.problem:
        problem_name = problem_args[0]
        files = problem_args[1:]

        if len(files) not in (2, 3):
            raise RuntimeError(
                f"{problem_name}: expected 2 or 3 VTU files, got {len(files)}"
            )

        a = read_vtu(files[0])
        b = read_vtu(files[1])

        max1, mean1, rel1 = _get_stats(a, b, args.field)
        comparisons = [(f"{args.labels[0]} vs {args.labels[1]}",
                        max1, mean1, rel1)]

        if len(files) == 3:
            c = read_vtu(files[2])

            # 2) Framework A vs Framework C
            max2, mean2, rel2 = _get_stats(a, c, args.field)

            # 3) Framework B vs Framework C
            max3, mean3, rel3 = _get_stats(b, c, args.field)

            comparisons.append(
                (f"{args.labels[0]} vs {args.labels[2]}",
                 max2, mean2, rel2))
            comparisons.append(
                (f"{args.labels[1]} vs {args.labels[2]}",
                 max3, mean3, rel3))

        print(problem_name)
        print(comparisons)
        problems.append((problem_name, comparisons))

    _plot(problems, output=args.output)


if __name__ == "__main__":
    main()
