DOCKER := podman
N := 20000
IMAGE_NAME := certfem-container
PETSC_CFLAGS := $(shell pkg-config --cflags PETSc)
PETSC_LIBS := $(shell pkg-config --libs PETSc)
CFLAGS := -g -O2
CC := mpicc

all:
	echo "See README.md and Makefile for targets."

.lake/build/lib/lean/CertFEM.olean: CertFEM.lean $(wildcard CertFEM/*.lean) lakefile.toml lake-manifest.json lean-toolchain
	lake build CertFEM

examples/%-$(N)-output.vtu: examples/%-$(N).out
	cd "$(dir $<)" && "./$(notdir $<)"

examples/%-$(N).out: examples/%-$(N).c
	$(CC) $(CFLAGS) $(PETSC_CFLAGS) -o $@ $< $(PETSC_LIBS)

examples/%-$(N).c: examples/%.lean .lake/build/lib/lean/CertFEM.olean
	cd examples && lake -d .. env lean --run $(notdir $<) $(N)

finch-examples/%-$(N)-output.vtu: finch-examples/%.jl
	cd "$(dir $<)" && julia "$(notdir $<)" $(N)

fenics-examples/%-$(N)-output.vtu: fenics-examples/%.py
	cd "$(dir $<)" && python3 "$(notdir $<)" $(N)

doc: docbuild/.lake/build/doc/index.html

docbuild/.lake/build/doc/index.html: docbuild/lakefile.toml CertFEM.lean
	cd docbuild; \
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4; \
  DOCGEN_SRC="file" lake build CertFEM:docs

show-doc: docbuild/.lake/build/doc/index.html
	cd docbuild/.lake/build/doc; python3 -m http.server
	xdg-open http://localhost:8000

error-$(N).png: scripts/graph_error.py
	python3 scripts/graph_error.py \
  --problem "Poisson" finch-examples/poisson-1d-$(N)-output.vtu \
                      fenics-examples/poisson-1d-$(N)-output_p0_000000.vtu \
                      examples/poisson-1d-$(N)-output.vtu \
  --problem "Convection-Diffusion" finch-examples/convection-diffusion-2d-$(N)-output.vtu \
                                   fenics-examples/convection-diffusion-2d-$(N)-output_p0_000000.vtu \
                                   examples/convection-diffusion-2d-$(N)-output.vtu \
  --problem "Reaction-Transport" finch-examples/convection-diffusion-reaction-2d-$(N)-output.vtu \
                                 fenics-examples/convection-diffusion-reaction-2d-$(N)-output_p0_000000.vtu \
                                 examples/convection-diffusion-reaction-2d-$(N)-output.vtu \
  --labels Finch FEniCS CertFEM

error-conv-$(N).png: scripts/graph_error.py
	python3 scripts/graph_error.py \
  --problem "Convection-Diffusion" finch-examples/convection-diffusion-2d-$(N)-output.vtu \
                                   fenics-examples/convection-diffusion-2d-$(N)-output_p0_000000.vtu \
                                   examples/convection-diffusion-2d-$(N)-output.vtu \
  --labels Finch FEniCS CertFEM

perf.png: scripts/graph_performance.py fenics-examples/results.csv finch-examples/results.csv examples/results.csv
	python3 scripts/graph_performance.py fenics-examples/results.csv \
    finch-examples/results.csv examples/results.csv

docker: Dockerfile
	$(DOCKER) build -t $(IMAGE_NAME) .

run-docker:
	$(DOCKER) run --rm -it -v "$(PWD):/work" $(IMAGE_NAME):latest
    # -v "$$HOME/.elan:/work/.elan"
    # -v "$$HOME/.cache/mathlib:/work/.cache/mathlib"

../certfem.zip:
	git archive --format=zip --output ../certfem.zip master

clean:
	rm -f error.png perf.png examples/*.c examples/*.vtu examples/*.out \
    finch-examples/*.vtu fenics-examples/*.pvd fenics-examples/*.vtu fenics-examples/*.pvtu

.PRECIOUS: examples/%-$(N).c examples/%-$(N).out
.PHONY: all doc clean docker run-docker show-doc
