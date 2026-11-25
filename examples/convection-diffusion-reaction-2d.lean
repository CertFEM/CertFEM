/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import Mathlib.Data.Nat.Sqrt
import CertFEM

-- LOC count starts
def lhs : TopLevel 2 := .Sum
  (.Integral (.mul .trial .test))
  (.Sum (.Integral (.mul (.pDeriv .gradTrial 0) .test))
    (.Coeff (1 / 10) (.inner .gradTest .gradTrial)))

theorem lhs_valid (s : Variational.ZeroBoundarySpace 2) : lhs.Valid s := by
  refine Exists.intro ((1 / 10 : Real) * s.coercivityConstant)
    (And.intro (mul_pos (by norm_num) s.coercivityConstant_pos) ?_)
  constructor
  case left =>
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, zero_add] using
      TopLevel.EnergyCertificate.sum
        (TopLevel.EnergyCertificate.integral
          (TopLevel.EnergyCertificate.commute_mul
            (TopLevel.EnergyCertificate.mass (s := s) 1 (by norm_num))))
        (TopLevel.EnergyCertificate.sum
          (TopLevel.EnergyCertificate.integral
            (TopLevel.EnergyCertificate.commute_mul
              (TopLevel.EnergyCertificate.gradient 1 0)))
          (TopLevel.EnergyCertificate.diffusion (1 / 10) (by norm_num)))
  case right =>
    change (0 < (1 : Realish)) /\ True /\ (0 < (1 / 10 : Realish))
    norm_num

def writeProg (stem : String) (n : PNat) : IO Unit := do
  let rhs := .Integral (.mul (.sReal (1 / 10)) .test)
  let mesh := unitSquareMesh n .falling
  let program := emitSolver lhs rhs mesh mesh.unitBoundary s!"{stem}-output.vtu"
  -- LOC count ends
  match program with
  | .ok code => writeImp s!"{stem}.c" code
  | .error message => throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [arg] := args | throw (IO.userError "Expected one mesh size argument")
  let some nElem := arg.toNat? | throw (IO.userError "Expected a natural number")
  let n := (nElem / 2).sqrt
  if h : 0 < n then
    writeProg s!"convection-diffusion-reaction-2d-{nElem}" (Subtype.mk n h)
  else
    throw (IO.userError "Mesh size must give at least one subdivision")
