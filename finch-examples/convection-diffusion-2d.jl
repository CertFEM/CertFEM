#=
# 2D Convection-Diffusion, Dirichlet bc, P1 triangles on the unit square
#   Integrators: Anisotropic Diffusion, Advection, Linear
#
#   int grad(v)^T D grad(u) dx + int v (vel . grad(u)) dx = int 5 v dx
#   D = [1.0 0.2; 0.2 0.5], vel = [1, 2]
#
# Dirichlet bc: u = 0 on the whole boundary
# Linear solve: PETSc, KSP preonly + PC LU (direct LU factorization)
=#
using Finch
initFinch("convection-diffusion-2d");
useLog("convection-diffusion-2d", level=3)

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
coefficient("D", [1.0 0.2; 0.2 0.5], type=TENSOR)
coefficient("vel", [1.0, 2.0], type=VECTOR)
coefficient("f", 5.0)
weakForm(u, "dot(matvec(D, grad(u)), grad(v)) + dot(vel, grad(u))*v - f*v")

solve(u);

outputValues(u, "convection-diffusion-2d-$(n)-output"; format="vtk", ascii=false)
finalizeFinch()
