"""
1D Poisson, Dirichlet bc, P1 line elements on the unit interval
  Integrators: Diffusion, Linear

  int grad(u).grad(v) dx = int 6 v dx

Dirichlet bc: u = 0 at both ends
Linear solve: PETSc, KSP preonly + PC LU (direct LU factorization)
"""
import sys
from time import perf_counter

from mpi4py import MPI
from dolfinx import mesh, fem, io
from dolfinx.fem.petsc import LinearProblem
import ufl


def run_sim(n):
    domain = mesh.create_unit_interval(MPI.COMM_SELF, n)
    V = fem.functionspace(domain, ("Lagrange", 1))
    domain.topology.create_connectivity(domain.topology.dim - 1, domain.topology.dim)
    boundary_dofs = fem.locate_dofs_topological(
        V, domain.topology.dim - 1, mesh.exterior_facet_indices(domain.topology))
    bc = fem.dirichletbc(fem.Constant(domain, 0.0), boundary_dofs, V)
    u = ufl.TrialFunction(V)
    v = ufl.TestFunction(V)
    f = fem.Constant(domain, 6.0)
    a = ufl.dot(ufl.grad(u), ufl.grad(v)) * ufl.dx
    L = f * v * ufl.dx
    return domain, bc, a, L


n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
t0 = perf_counter()
domain, bc, a, L = run_sim(n)
problem = LinearProblem(a, L, bcs=[bc],
                        # petsc_options_prefix="poisson_1d_",
                        petsc_options={"ksp_type": "preonly",
                                       "pc_type": "lu",
                                       "pc_factor_mat_solver_type": "petsc"})
u = problem.solve()
print(f"Completed in {perf_counter() - t0} seconds")

u.name = "u"
with io.VTKFile(domain.comm, f"poisson-1d-{n}-output.pvd", "w") as vtk:
    vtk.write_function(u)
