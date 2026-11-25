FROM debian:trixie-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl git ca-certificates build-essential file \
    python3 python3-pip python3-venv python3-numpy \
    python3-dolfinx petsc-dev pkg-config python3-meshio python3-matplotlib

ENV ELAN_HOME=/root/.elan
ENV PATH="/root/.elan/bin:/root/.juliaup/bin:/root/.local/bin:${PATH}"

RUN curl -fsSL https://install.julialang.org | \
  sh -s -- --yes --default-channel 1.7.3 && \
  julia -e 'using Pkg; Pkg.add(url="https://github.com/CertFEM/Finch.git")'

RUN curl -sSf https://elan.lean-lang.org/elan-init.sh \
    | sh -s -- -y --default-toolchain leanprover/lean4:v4.30.0

WORKDIR /work
CMD ["/bin/sh"]
