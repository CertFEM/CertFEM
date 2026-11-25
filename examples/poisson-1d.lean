/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM

-- LOC count starts
def lhs : TopLevel 1 := .Integral (.inner .gradTest .gradTrial)

theorem lhs_valid (s : Variational.ZeroBoundarySpace 1) : lhs.Valid s := by
  refine Exists.intro s.coercivityConstant
    (And.intro s.coercivityConstant_pos ?_)
  constructor
  case left =>
    simpa only [Rat.cast_one, one_mul] using
      TopLevel.EnergyCertificate.integral
        (TopLevel.EnergyCertificate.diffusion (s := s) 1 (by norm_num))
  case right =>
    norm_num [lhs, TopLevel.checkCoeffs, matchPCI, pciSpecification, diffusionPCI]

def writeProg (stem : String) (n : PNat) : IO Unit := do
  let rhs := .Integral (.mul (.sReal 6) .test)
  let mesh := unitLineMesh n
  let program := emitSolver lhs rhs mesh mesh.unitBoundary s!"{stem}-output.vtu"
  -- LOC count ends
  match program with
  | .ok code => writeImp s!"{stem}.c" code
  | .error message => throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [arg] := args | throw (IO.userError "Expected one mesh size argument")
  let some nElem := arg.toNat? | throw (IO.userError "Expected a natural number")
  let n := nElem
  if h : 0 < n then
    writeProg s!"poisson-1d-{nElem}" (Subtype.mk n h)
  else
    throw (IO.userError "Mesh size must give at least one subdivision")
