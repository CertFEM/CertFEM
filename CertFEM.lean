/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.Basic

/-- Generate a C solver that writes its solution to the requested VTU path. -/
def emitSolver {dim nv nt : Nat} (lhs rhs : TopLevel dim)
    (mesh : Mesh dim nv nt) (boundary : List (Fin nv)) (filename : String) :
    Except String String :=
  solve lhs rhs mesh boundary filename

def writeImp (fname txt : String) : IO Unit :=
  IO.FS.writeFile fname txt

/-- Generate a solver with a configurable rational approximation tolerance. -/
def emitSolverWithOptions {dim nv nt : Nat} (options : CompilerOptions)
    (lhs rhs : TopLevel dim) (mesh : Mesh dim nv nt) (boundary : List (Fin nv))
    (filename : String) : Except String String :=
  solveWithOptions options lhs rhs mesh boundary filename
