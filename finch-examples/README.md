***important***: use Julia version 1.7

## Add Finch package using Julia packages

```
julia -e 'using Pkg; Pkg.add(url="https://github.com/CertFEM/Finch.git")'
```

## Run examples

Run from inside `finch-examples`. `<mesh size>` is the number of elements per
dimension (for the 2D examples, each square is split into 2 triangles); default 100.

```bash
julia --project=. poisson-1d.jl <mesh size>
julia --project=. convection-diffusion-2d.jl <mesh size>
julia --project=. convection-diffusion-reaction-2d.jl <mesh size>
```

Each script prints a timing report and writes the solution to
`<example>-output.vtu`.

| Script | PDE (weak form) |
|---|---|
| `poisson-1d.jl` | ∫∇u·∇v = ∫6v (1D) |
| `convection-diffusion-2d.jl` | ∫(∇v)ᵀD∇u + ∫v(vel·∇u) = ∫5v, D = [1.0 0.2; 0.2 0.5], vel = [1, 2] |
| `convection-diffusion-reaction-2d.jl` | ∫uv + ∫(∂u/∂x)v + eps∫∇u·∇v = ∫0.1v, eps = 0.1 |

Poisson uses P1 line elements on the unit interval; the other two use P1
triangles on the unit square. All use Dirichlet boundary condition u = 1 and
solve the linear system with PETSc (KSP preonly + PC LU).
