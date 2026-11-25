"""
2D Convection-Diffusion, Dirichlet bc, P1 triangles on the unit square
  Integrators: Anisotropic Diffusion, Advection, Linear

  int grad(v)^T D grad(u) dx + int v (vel . grad(u)) dx = int 5 v dx
  D = [1.0 0.2; 0.2 0.5], vel = [1, 2]

Dirichlet bc: u = 0 on the whole boundary
Linear solve: PETSc, KSP preonly + PC LU (direct LU factorization)
"""
import sys
from time import perf_counter
from math import sqrt

import numpy as np
from mpi4py import MPI
from dolfinx import mesh, fem, io
from dolfinx.fem.petsc import LinearProblem
import ufl


def run_sim(n):
    domain = mesh.create_unit_square(MPI.COMM_SELF, n, n, mesh.CellType.triangle,
                                     diagonal=mesh.DiagonalType.left)
    V = fem.functionspace(domain, ("Lagrange", 1))
    domain.topology.create_connectivity(domain.topology.dim - 1, domain.topology.dim)
    boundary_dofs = fem.locate_dofs_topological(
        V, domain.topology.dim - 1, mesh.exterior_facet_indices(domain.topology))
    bc = fem.dirichletbc(fem.Constant(domain, 0.0), boundary_dofs, V)
    u = ufl.TrialFunction(V)
    v = ufl.TestFunction(V)
    D = fem.Constant(domain, np.array([[1.0, 0.2], [0.2, 0.5]]))
    vel = fem.Constant(domain, np.array([1.0, 2.0]))
    f = fem.Constant(domain, 5.0)
    a = (ufl.dot(ufl.grad(v), D * ufl.grad(u)) * ufl.dx
         + v * ufl.dot(vel, ufl.grad(u)) * ufl.dx)
    L = f * v * ufl.dx
    return domain, bc, a, L


n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
nx = int(sqrt(n // 2))
t0 = perf_counter()
domain, bc, a, L = run_sim(nx)
problem = LinearProblem(a, L, bcs=[bc],
                        # petsc_options_prefix="convection_diffusion_2d_",
                        petsc_options={"ksp_type": "preonly",
                                       "pc_type": "lu",
                                       "pc_factor_mat_solver_type": "petsc"})
u = problem.solve()
print(f"Completed in {perf_counter() - t0} seconds")

u.name = "u"
with io.VTKFile(domain.comm, f"convection-diffusion-2d-{n}-output.pvd", "w") as vtk:
    vtk.write_function(u)
