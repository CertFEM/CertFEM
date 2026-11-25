#=
# 2D Convection-Diffusion-Reaction, Dirichlet bc, P1 triangles on the unit square
#   Integrators: Mass, Gradient (x component), Diffusion, Linear
#   (convection with vel = [1, 0], plus reaction and a small diffusion term)
#
#   int u v dx + int du/dx v dx + eps int grad(u).grad(v) dx = int 0.1 v dx
#   eps = 0.1 (small diffusion so the outflow boundary layer is stable)
#
# Dirichlet bc: u = 0 on the whole boundary
# Linear solve: PETSc, KSP preonly + PC LU (direct LU factorization)
=#
using Finch
initFinch("convection-diffusion-reaction-2d");
useLog("convection-diffusion-reaction-2d", level=3)

linAlgOptions(pc="LU")
usePetsc()

n = length(ARGS) >= 1 ? parse(Int, ARGS[1]) : 100;
nx = floor(Int, sqrt(n / 2))

# LOC count for this block
domain(2)
functionSpace(order=1)
mesh(TRIMESH, elsperdim=nx)
u = variable("u")
testSymbol("v")
boundary(u, 1, DIRICHLET, 0.0)
coefficient("eps", 0.1)
coefficient("f", 0.1)
weakForm(u, "u*v + deriv(u, 1)*v + eps*dot(grad(u), grad(v)) - f*v")

solve(u);

outputValues(u, "convection-diffusion-reaction-2d-$(n)-output"; format="vtk", ascii=false)
finalizeFinch()
