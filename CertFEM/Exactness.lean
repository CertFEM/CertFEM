/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.DefPCI
import CertFEM.Basis
import CertFEM.Duffy

/-! # Concrete quadrature exactness (Sections 6.3-6.4). -/

/-- Paper "Quadrature Parameters": three Gauss points integrate every P1 mass product exactly. -/
theorem massP1ThreePtExact (basis : P1Basis 1)
    (hbasis : forall i, (basis i).totalDegree <= 1) (i j : Fin 2) :
    (massPCI 1).integral (basis i) (basis j) =
      (massPCI 1).accumulator threePtQuad basis 1 i j := by
  apply massP1Exact basis hbasis threePtQuad _ i j
  intro p hp
  exact ThreePtExact p (hp.trans (by norm_num))

/-- Paper "Generalizing Quadrature to Higher Dimensions with the Duffy Transform":
the concrete two-dimensional rule is exact for every P1 mass product. -/
theorem massP1DuffyExact (basis : P1Basis 2)
    (hbasis : forall i, (basis i).totalDegree <= 1) (i j : Fin 3) :
    (massPCI 2).integral (basis i) (basis j) =
      (massPCI 2).accumulator (duffyTransform threePtQuad 2) basis 1 i j :=
  massP1Exact basis hbasis _ DuffyExact2D2 i j

/-- Paper theorem "Mass Integrator Quadrature Exactness": the three distinct
one-dimensional mass entries computed by the exact Gauss rule. -/
theorem massThreePtEntries (i j : Fin 2) :
    quadSum threePtQuad 1 (fun g =>
      basisAt threePtQuad basisFunc1D g i * basisAt threePtQuad basisFunc1D g j) =
      if i = j then (2 : Real) / 3 else 1 / 3 := by
  have hs : Real.sqrt ((3 : Real) / 5) ^ 2 = (3 : Real) / 5 :=
    Real.sq_sqrt (by norm_num)
  simp only [quadSum, basisAt, threePtQuad]
  generalize hr : Real.sqrt ((3 : Real) / 5) = r at *
  fin_cases i <;> fin_cases j <;>
    norm_num [basisFunc1D, Fin.sum_univ_succ] <;> nlinarith

/-- Paper theorem "Mass Integrator Quadrature Exactness": the actual interval integrals
of the canonical basis products, independently of the algebraic reference-moment definition. -/
theorem massIntervalEntries (i j : Fin 2) :
    intervalIntegral (fun x : Real =>
      evalPoly (basisFunc1D i) (fun _ => x) * evalPoly (basisFunc1D j) (fun _ => x))
      (-1 : Real) 1 MeasureTheory.volume =
      if i = j then (2 : Real) / 3 else 1 / 3 := by
  fin_cases i <;> fin_cases j
  all_goals
    conv_lhs =>
      arg 1
      ext x
      simp [evalPoly, basisFunc1D]
      ring_nf
    simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
      [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
       intervalIntegral.integral_const, integral_id, integral_pow]
    norm_num

/-- Paper theorem "Mass Integrator Quadrature Exactness", analytic interval statement. -/
theorem massThreePtExact (i j : Fin 2) :
    intervalIntegral (fun x : Real =>
      evalPoly (basisFunc1D i) (fun _ => x) * evalPoly (basisFunc1D j) (fun _ => x))
      (-1 : Real) 1 MeasureTheory.volume =
      quadSum threePtQuad 1 (fun g =>
        basisAt threePtQuad basisFunc1D g i * basisAt threePtQuad basisFunc1D g j) := by
  rw [massIntervalEntries, massThreePtEntries]
