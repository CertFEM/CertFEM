"""Noncoercive Reaction-Transport (not used in paper evaluation)"""
import sys
from time import perf_counter
from math import sqrt

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
    eps = fem.Constant(domain, -0.0000333333)
    f = fem.Constant(domain, 1.0)
    a = (u * v * ufl.dx
         + u.dx(0) * v * ufl.dx
         + eps * ufl.dot(ufl.grad(u), ufl.grad(v)) * ufl.dx)
    L = f * v * ufl.dx
    return domain, bc, a, L


n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
nx = int(sqrt(n // 2))
t0 = perf_counter()
domain, bc, a, L = run_sim(nx)
problem = LinearProblem(a, L, bcs=[bc],
                        # petsc_options_prefix="convection_diffusion_reaction_2d_",
                        petsc_options={"ksp_type": "preonly",
                                       "pc_type": "lu",
                                       "pc_factor_mat_solver_type": "petsc"})
u = problem.solve()
print(f"Completed in {perf_counter() - t0} seconds")

u.name = "u"
with io.VTKFile(domain.comm, f"noncoercive-2d-{n}-output.pvd", "w") as vtk:
    vtk.write_function(u)
