#=
# 1D Poisson, Dirichlet bc, P1 line elements on the unit interval
#   Integrators: Diffusion, Linear
#
#   int grad(u).grad(v) dx = int 6 v dx
#
# Dirichlet bc: u = 0 at both ends
# Linear solve: PETSc, KSP preonly + PC LU (direct LU factorization)
=#
using Finch
initFinch("poisson-1d");
useLog("poisson-1d", level=3)

linAlgOptions(pc="LU")
usePetsc()

n = length(ARGS) >= 1 ? parse(Int, ARGS[1]) : 100;

# LOC count for this block
domain(1)
functionSpace(order=1)
mesh(LINEMESH, elsperdim=n)
u = variable("u")
testSymbol("v")
boundary(u, 1, DIRICHLET, 0.0)
coefficient("f", 6.0)
weakForm(u, "dot(grad(u), grad(v)) - f*v")

solve(u);

outputValues(u, "poisson-1d-$(n)-output"; format="vtk", ascii=false)
finalizeFinch()
