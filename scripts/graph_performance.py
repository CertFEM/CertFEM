#!/usr/bin/env python3

import argparse
import csv
import matplotlib.pyplot as plt


def parse_files(files):
    # data[problem][label] = [(mesh, time), ...]
    data = {}

    for f in files:
        with open(f, newline="") as csvfile:
            reader = csv.DictReader(csvfile)

            for row in reader:
                problem = row["Problem"]
                solver = row["Solver"]

                mesh = float(row["Mesh Size (# Elements)"])
                time = float(row["Time (s)"])

                label = solver

                # manual initialization (no defaultdict)
                if problem not in data:
                    data[problem] = {}
                if label not in data[problem]:
                    data[problem][label] = []

                data[problem][label].append((mesh, time))

    return data


def plot_slide(data, problems):
    fig, axes = plt.subplots(
        1, len(problems),
        figsize=(4 * len(problems), 3.5),
        squeeze=False
    )

    solver_order = ["FEniCS", "CertFEM"]

    for i, problem in enumerate(problems):
        ax = axes[0, i]

        for label in solver_order:
            values = sorted(data[problem][label])
            mesh = [v[0] for v in values]
            time = [v[1] for v in values]

            ax.plot(mesh, time, marker="o", label=label)

        if problem == "Convection-Diffusion":
            ax.set_title("2D Convection-Diffusion")
        elif problem == "Convection-Diffusion-Reaction":
            ax.set_title("2D Reaction-Transport")
        elif problem == "Poisson 1D":
            ax.set_title("1D Poisson")
        else:
            ax.set_title(problem)

        ax.set_xlabel("Mesh Size (# Elements)")
        ax.set_ylabel("Solve Time (s)")
        ax.set_ylim(bottom=0)
        ax.grid(True, linestyle="--", linewidth=0.5)

    axes[0, -1].legend(loc="upper left")
    fig.tight_layout()

    return fig


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("csv_files", nargs="+", help="Input CSV files")
    parser.add_argument("--output", default="perf.png")
    parser.add_argument("--slide", action="store_true", help="Figure for slides")
    args = parser.parse_args()

    data = parse_files(args.csv_files)
    problems = sorted(data.keys())

    if args.slide:
        fig = plot_slide(data, ["Convection-Diffusion",
                                "Convection-Diffusion-Reaction",
                                "Poisson 1D"])
        fig.savefig(args.output, dpi=300, bbox_inches="tight")
        plt.show()
        return

    fig, axes = plt.subplots(
        2, len(problems),
        figsize=(5 * len(problems), 5),
        sharex="col")

    if len(problems) == 1:
        axes = axes.reshape(2, 1)

    for i, problem in enumerate(problems):
        top = axes[0, i]
        bottom = axes[1, i]

        # Plot the same data on both halves of the broken axis.
        for label, values in data[problem].items():
            values.sort()
            mesh = [v[0] for v in values]
            time = [v[1] for v in values]

            top.plot(mesh, time, marker="o", label=label)
            bottom.plot(mesh, time, marker="o", label=label)

        # Only these two y ranges are displayed.
        top.set_ylim(22, 65)
        bottom.set_ylim(0, 15)

        if problem == "Convection-Diffusion-Reaction":
            top.set_title("Reaction-Transport")
        else:
            top.set_title(problem)
        bottom.set_xlabel("Mesh Size (# Elements)")

        # Remove the border where the y axis is broken.
        top.spines["bottom"].set_visible(False)
        bottom.spines["top"].set_visible(False)
        top.tick_params(axis="x", bottom=False, labelbottom=False)

        # Draw the break marks.
        d = 0.015
        top.plot((-d, d), (-d, d), transform=top.transAxes,
                 color="k", clip_on=False)
        bottom.plot((-d, d), (1-d, 1+d), transform=bottom.transAxes,
                    color="k", clip_on=False)

        top.grid(True, linestyle="--", linewidth=0.5)
        bottom.grid(True, linestyle="--", linewidth=0.5)

    axes[0, 0].set_ylabel("Time (s)")
    axes[1, 0].set_ylabel("Time (s)")

    handles, labels = axes[0, -1].get_legend_handles_labels()
    axes[1, 1].legend(handles, labels, loc="upper center")
    # fig.legend(handles, labels, loc="lower center")
    # fig.subplots_adjust(bottom=0.25)

    plt.show()
    if args.output is not None:
        fig.savefig(args.output, dpi=300, bbox_inches="tight")


if __name__ == "__main__":
    main()
