/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import Mathlib
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import CertFEM.Util

/-! # Simplexes -/

def refSimplex1D : Affine.Simplex Realish (Fin 1 -> Realish) 1 where
  points := ![![-1], ![1]]
  independent := by
    apply affineIndependent_of_ne Realish
    intro h
    have h0 := congrArg (fun p : Fin 1 -> Realish => p 0) h
    norm_num at h0

def simplexND (dim : Nat) : Affine.Simplex Realish (Fin dim -> Realish) dim where
  points := Fin.cons 0 (fun i => Pi.single i (1 : Realish))
  independent := by
    classical
    let pts : Fin (dim + 1) -> (Fin dim -> Realish) :=
      Fin.cons 0 (fun i => Pi.single i (1 : Realish))
    change AffineIndependent Realish pts
    apply (affineIndependent_iff_linearIndependent_vsub
      Realish pts (0 : Fin (dim + 1))).mpr
    apply (linearIndependent_equiv
      (finSuccAboveEquiv (0 : Fin (dim + 1)))).mp
    simpa [pts, Function.comp_def, finSuccAboveEquiv_apply,
      vsub_eq_sub] using
      (Pi.linearIndependent_single_one (Fin dim) Realish)

def refSimplexND (dim : Nat)
    : Affine.Simplex Realish (Fin dim -> Realish) dim := by
  if h : dim = 1 then
    subst dim
    exact refSimplex1D
  else
    exact simplexND dim

def realDomainOfSimplex {dim : Nat}
    (s : Affine.Simplex Realish (Fin dim -> Realish) dim)
    : Set (Fin dim -> Real) :=
  convexHull Real
    (Set.range (fun i : Fin (dim + 1) =>
      fun k : Fin dim => (s.points i k : Real)))
