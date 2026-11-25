/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import Mathlib.Data.Nat.Sqrt
import CertFEM

-- LOC count starts
def tensor : DiffusionTensor 2 := !![1, 1 / 5; 1 / 5, 1 / 2]
def velocity : VelocityVector 2 := ![1, 2]

def lhs : TopLevel 2 := .Sum
  (.Integral (.inner .gradTest (.matMul tensor .gradTrial)))
  (.Integral (.mul .test (.inner (.velVec velocity) .gradTrial)))

theorem tensor_uniformElliptic :
    Variational.Space.UniformElliptic (tensor.map (algebraMap Realish Real)) (3 / 10) := by
  intro z
  norm_num [tensor, Matrix.map_apply, Fin.sum_univ_two]
  nlinarith [sq_nonneg (z 0), sq_nonneg (z 0 + z 1)]

theorem lhs_valid (s : Variational.ZeroBoundarySpace 2) : lhs.Valid s := by
  refine Exists.intro ((3 / 10 : Real) * s.coercivityConstant)
    (And.intro (mul_pos (by norm_num) s.coercivityConstant_pos) ?_)
  constructor
  case left =>
    simpa only [Rat.cast_one, one_mul, add_zero] using
      TopLevel.EnergyCertificate.sum
        (TopLevel.EnergyCertificate.integral
          (TopLevel.EnergyCertificate.anisotropic (s := s) 1
            (by norm_num) tensor (3 / 10) (by norm_num)
            tensor_uniformElliptic))
        (TopLevel.EnergyCertificate.integral
          (TopLevel.EnergyCertificate.advection 1 velocity))
  case right =>
    change (0 < (1 : Realish)) /\ True
    norm_num

def writeProg (stem : String) (n : PNat) (diagonal : SquareDiagonal) : IO Unit := do
  let rhs := .Integral (.mul (.sReal 5) .test)
  let mesh := unitSquareMesh n diagonal
  let program := emitSolver lhs rhs mesh mesh.unitBoundary s!"{stem}-output.vtu"
  -- LOC count ends
  match program with
  | .ok code => writeImp s!"{stem}.c" code
  | .error message => throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let (arg, diagonal, suffix) <- match args with
    | [arg] => pure (arg, SquareDiagonal.falling, "")
    | [arg, "--fenics-mesh"] => pure (arg, SquareDiagonal.rising, "-fenics-mesh")
    | _ => throw (IO.userError "Expected a mesh size and optional --fenics-mesh")
  let some nElem := arg.toNat? | throw (IO.userError "Expected a natural number")
  let n := (nElem / 2).sqrt
  if h : 0 < n then
    writeProg s!"convection-diffusion-2d-{nElem}{suffix}" (Subtype.mk n h) diagonal
  else
    throw (IO.userError "Mesh size must give at least one subdivision")
