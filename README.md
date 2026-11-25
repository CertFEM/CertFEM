
# CertFEM

CertFEM is a formally verified FEM/FEA package developed in Lean 4.
It can solve a range of PDEs using the included (proof-carrying) integrators,
and emits C code that can be compiled and run with good performance.
It aims to verify or prove the following FEM correctness properties:

1. User-provided weak forms are bounded and coercive (Lax-Milgram).
2. Quadrature schemes (points/weights) are mathematically correct.
3. Quadrature is exact for all supported integrands.
4. Meshes are non-degenerate.
5. Meshes are conforming and connected.
6. Compilation is semantics-preserving.
7. Denotation of emitted global assembly code matches its mathematical specfication.

This repository is the artifact for the paper ["CertFEM: Proof-Carrying Integrators for Compositional
Verification of Finite-Element Form Compilation"](https://doi.org).
The paper is also [included here](./CertFEM-paper.pdf) for reference.

# Paper to formalization table

| Paper result                                      | Lean file and declarations                                                                                                                                                                                                                                             |
|---------------------------------------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Grammar/integrand/accumulator equivalence         | [DefPCI.lean](CertFEM/DefPCI.lean): `*FormOk`, `*AccOk`                                                                                                                                                                                                                |
| (Bi-)linearity of integrators                     | [DefPCI.lean](CertFEM/DefPCI.lean): `massBilinear`, `diffusionBilinear`, `gradientBilinear`, `anisotropicDiffusionBilinear`, `advectionBilinear`, `linearIntegratorLinear`                                                                                             |
| Proof-carrying integrator boundedness             | [Boundedness.lean](CertFEM/Boundedness.lean): `Variational.Space.bound_sum`, `TopLevel.bounded_of_certificate`, `TopLevel.bounded`                                                                                                                                     |
| Boundedness of the Mass Integrator                | [Boundedness.lean](CertFEM/Boundedness.lean): `massIntegratorBounded`, `Variational.Space.mass_bound`                                                                                                                                                                  |
| Boundedness of the other integrators              | [Boundedness.lean](CertFEM/Boundedness.lean): `Variational.Space.diffusion_bound`, `gradient_bound`, `advection_bound`, `anisotropic_bound`, `linear_bound`                                                                                                            |
| PCI coercivity                                    | [Coercivity.lean](CertFEM/Coercivity.lean): `Variational.ZeroBoundarySpace.diffusion_coercive`, `anisotropic_coercive`, `composition_coercive`, `TopLevel.coercive_of_valid`                                                                                           |
| Validity of example weak forms (`TopLevel.Valid`) | [poisson-1d.lean](examples/poisson-1d.lean): `lhs_valid`; [convection-diffusion-2d.lean](examples/convection-diffusion-2d.lean): `lhs_valid`; [convection-diffusion-reaction-2d.lean](examples/convection-diffusion-reaction-2d.lean): `lhs_valid`                     |
| Skew-symmetry of the Advection PCI                | [Coercivity.lean](CertFEM/Coercivity.lean): `Variational.ZeroBoundarySpace.advection_skew`, `gradient_skew`                                                                                                                                                            |
| Coercivity to nonsingularity                      | [Coercivity.lean](CertFEM/Coercivity.lean): `stiffness_nonsingular_of_energy`                                                                                                                                                                                          |
| Quadrature points and weights                     | [Quad.lean](CertFEM/Quad.lean): `threePtIsGauss`, `ThreePtExact`                                                                                                                                                                                                       |
| Generalizing Quadrature with the Duffy Transform  | [Duffy.lean](CertFEM/Duffy.lean): `duffyTransform`, `DuffyExact2D2`; [Exactness.lean](CertFEM/Exactness.lean): `massP1DuffyExact`                                                                                                                                      |
| Mass Integrator Quadrature Exactness              | [DefPCI.lean](CertFEM/DefPCI.lean): `massP1Exact`; [Exactness.lean](CertFEM/Exactness.lean): `massP1ThreePtExact`, `massThreePtEntries`, `massIntervalEntries`, `massThreePtExact`                                                                                     |
| Mesh Non-degeneracy                               | [MeshValidity.lean](CertFEM/MeshValidity.lean): `unitLineMesh_nondegenerate`, `unitSquareMesh_nondegenerate`; [Mesh.lean](CertFEM/Mesh.lean): `Mesh.edgeVectorsIndependent`, `Mesh.edgeCombination_ne_zero`                                                            |
| Mesh Conformity                                   | [MeshValidity.lean](CertFEM/MeshValidity.lean): `unitLineMesh_conforming`, `unitLineMesh_connected`, `unitLineMesh_valid`, `unitSquareMesh_conforming`, `unitSquareMesh_connected`, `unitSquareMesh_valid`; [Mesh.lean](CertFEM/Mesh.lean): `Mesh.toSimplicialComplex` |
| Denotational Equivalence of Scatter-Add Code      | [Assembly.lean](CertFEM/Assembly.lean): `scatterMatrix_denote`, `scatterLoad_denote`, `assembleMatrices_denote`; [Semantics.lean](CertFEM/Semantics.lean): `elementAssembly_matrix`, `elementAssembly_load`, `compiledMesh_denote`                                     |
| Applying Top-Level Operations                     | [Assembly.lean](CertFEM/Assembly.lean): `scatterMatrixSpec_scale`, `scatterMatrixSpec_add`; [Semantics.lean](CertFEM/Semantics.lean): `compileKernels_denote`, `compileLoadKernels_denote`                                                                             |
| Imposing Boundary Conditions                      | [Boundaries.lean](CertFEM/Boundaries.lean): `imposeBoundary_denote`, `imposeBoundaryBulk_denote`, `imposeBoundary_interior`, `imposeBoundary_load_interior`, `imposeBoundary_diagonal`, `imposeBoundary_offDiagonal`                                                   |
| Semantics-Preserving FEM compilation in CertFEM   | [Assembly.lean](CertFEM/Assembly.lean): `QuadExpr.toImp_denote`, `compileIntegral_denote`, `compileLinear_denote`; [Semantics.lean](CertFEM/Semantics.lean): `compileIntegral_exact`, `compiledElement_denote`, `compiledSystem_denote`                                |
| Rational approximation boundary                   | [Approximation.lean](CertFEM/Approximation.lean): `rationalizeQuad_close`, `approximateNatSqrt_close`, `approximateThreePt_close`, `quadSum_error`, `quadSum_error_of_close`                                                                                           |

Note that the Rational approximation code in `Approximation.lean` was not
discussed in the paper.
It exists solely to verify that Lean Rational to Real number conversions do
not introduce excessive error above a fixed tolerance.

# Citing

If you use this repository, please cite:

```
TBD
```

# Usage

See the [example problems](./examples).
They are small and self-contained, and have all the information necessary to
construct any supported PDE.

The
[Mathlib 4](https://leanprover-community.github.io/mathlib4_docs/) documentation
will be helpful.

# Building

Use the `Dockerfile` to launch a Docker container with this directory bind-mounted:

```
docker build -t myimage .
docker run --rm -it -v "$PWD":/work -w /work myimage:latest
```

Or try the Makefile:

```
make docker DOCKER=docker
make run-docker DOCKER=docker
```

## Building documentation

Run `make doc` to generate documentation using `doc-gen4`.
Warning that this may take a very long time (even an hour).

Run `make show-doc` outside the container to set up a HTTP server using Python
and launch your browser using `xdg-open`.
Alternatively, view the generated files in `docbuild/.lake/build/doc`.

# Reproducing results

## Performance

For Finch, run `julia finch-examples/<PROBLEM>.jl <ELEMS>`, where
`PROBLEM` is the file name of the problem to run, and `ELEMS` is the number of elements.
You will see a report of measure times.
Paste results into `finch-examples/results.csv`.

For FEniCS, run `python3 <PROBLEM>.py <ELEMS>` from inside `fenics-examples`.
You will see a print of the time taken.
Paste results into `fenics-examples/results.csv`.

For CertFEM, replace `poisson-1d` with the desired example name and set `N`
to the requested element count:

```sh
make examples/poisson-1d-20000.out N=20000
cd examples
time ./poisson-1d-20000.out
```

The executable writes `poisson-1d-20000-output.vtu` in its working directory.
Paste results into `examples/results.csv`.

To generate and view the performance graph, run:
```
make perf.png
```

## Error

Make sure the <ELEM>-element VTU files are generated for each framework by
running the examples.
Then run:
```
make error-<ELEMS>.png N=<ELEM>
```

## Lines of code

The values for this figure were collected manually. Do not count comments, blank
spaces, any code to invoke the solver, any code to set up logging or printing,
or import statements.

For the FEniCS examples, only count the code in the `run_sim` function, minus
the function's signature line and return statement.
