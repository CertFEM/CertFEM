/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import Mathlib
import CertFEM.Util
import CertFEM.Simplex

/-! # Basis functions -/

noncomputable def basisFunc1D : Fin 2 -> MvPolynomial (Fin 1) Realish :=
  ![
    MvPolynomial.C (1 / 2 : Realish) * ((1 : MvPolynomial (Fin 1) Realish) - MvPolynomial.X 0),
    MvPolynomial.C (1 / 2 : Realish) * ((1 : MvPolynomial (Fin 1) Realish) + MvPolynomial.X 0)
  ]

noncomputable def basisFunc2D : Fin 3 -> MvPolynomial (Fin 2) Realish :=
  ![
    MvPolynomial.C (1 : Realish) - MvPolynomial.X 0 - MvPolynomial.X 1,
    MvPolynomial.X 0,
    MvPolynomial.X 1
  ]

noncomputable def basisFuncND (dim : Nat)
                  : Fin (dim + 1) -> MvPolynomial (Fin dim) Realish :=
  let coord : Fin dim -> MvPolynomial (Fin dim) Realish :=
    fun k =>
      if dim = 1 then
        MvPolynomial.C (1 / 2 : Realish) * (1 + MvPolynomial.X k)
      else
        MvPolynomial.X k
  Fin.cons (1 - Finset.univ.sum coord) coord

def basisFuncIs1AtVertex {dim : Nat}
    (s : Affine.Simplex Realish (Fin dim -> Realish) dim)
    (f : Fin (dim + 1) -> MvPolynomial (Fin dim) Realish) : Prop :=
  forall i : Fin (dim + 1),
    MvPolynomial.eval (s.points i) (f i) = 1

def basisFuncIs0AtOtherVertices {dim : Nat}
    (s : Affine.Simplex Realish (Fin dim -> Realish) dim)
    (f : Fin (dim + 1) -> MvPolynomial (Fin dim) Realish) : Prop :=
  forall i j : Fin (dim + 1), i != j ->
    MvPolynomial.eval (s.points j) (f i) = 0

def basisFuncIsP1 {dim : Nat}
    (f : Fin (dim + 1) -> MvPolynomial (Fin dim) Realish) : Prop :=
  forall i : Fin (dim + 1),
    (f i).totalDegree <= 1

def basisFuncInL2 {dim : Nat}
    (s : Affine.Simplex Realish (Fin dim -> Realish) dim)
    (b : Fin (dim + 1) -> MvPolynomial (Fin dim) Realish) : Prop :=
  forall i : Fin (dim + 1),
    MeasureTheory.MemLp
      (fun x : Fin dim -> Real =>
        MvPolynomial.eval x
          (MvPolynomial.map (algebraMap Realish Real) (b i)))
      2
      (MeasureTheory.volume.restrict (realDomainOfSimplex s))

private lemma basisCoordDegree (dim : Nat) (k : Fin dim) :
    (if dim = 1 then
      MvPolynomial.C (1 / 2 : Realish) *
        (1 + MvPolynomial.X k)
    else
      MvPolynomial.X k :
        MvPolynomial (Fin dim) Realish).totalDegree <= 1 := by
  by_cases h : dim = 1
  case pos =>
    simp only [if_pos h]
    calc
      (MvPolynomial.C (1 / 2 : Realish) *
        (1 + MvPolynomial.X k)).totalDegree
          <= (MvPolynomial.C (1 / 2 : Realish)).totalDegree +
             (1 + MvPolynomial.X k).totalDegree :=
               MvPolynomial.totalDegree_mul _ _
      _ <= 1 := by
        simpa using
          (MvPolynomial.totalDegree_add
            (1 : MvPolynomial (Fin dim) Realish)
            (MvPolynomial.X k))
  case neg =>
    simp [h]

lemma basisNDIsP1 : forall dim : Nat, basisFuncIsP1 (basisFuncND dim) := by
  intro dim
  change forall i : Fin (dim + 1),
    (basisFuncND dim i).totalDegree <= 1
  intro i

  let coord : Fin dim -> MvPolynomial (Fin dim) Realish :=
    fun k =>
      if dim = 1 then
        MvPolynomial.C (1 / 2 : Realish) *
          (1 + MvPolynomial.X k)
      else
        MvPolynomial.X k

  have hc : forall k : Fin dim, (coord k).totalDegree <= 1 := by
    intro k
    exact basisCoordDegree dim k

  have hs : (Finset.univ.sum coord).totalDegree <= 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    exact hc k

  cases i using Fin.cases with
  | zero =>
      change (1 - Finset.univ.sum coord).totalDegree <= 1
      exact (MvPolynomial.totalDegree_sub _ _).trans
        (max_le (by simp) hs)
  | succ k =>
      change (coord k).totalDegree <= 1
      exact hc k

private lemma basisNDEvalAtVertex (dim : Nat)
    (i j : Fin (dim + 1)) :
    MvPolynomial.eval ((refSimplexND dim).points j)
      (basisFuncND dim i) =
        if i = j then (1 : Realish) else 0 := by
  classical
  by_cases h : dim = 1
  case pos =>
    subst dim
    fin_cases i <;> fin_cases j <;>
      norm_num [basisFuncND, refSimplexND, refSimplex1D,
        MvPolynomial.eval_sum]
  case neg =>
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        simp [basisFuncND, refSimplexND, simplexND, h,
          MvPolynomial.eval_sum, Pi.single_apply]
      | succ k =>
        simp [basisFuncND, refSimplexND, simplexND, h,
          MvPolynomial.eval_sum, Pi.single_apply,
          Finset.sum_ite_eq, Finset.sum_ite_eq']
        exact Fin.succ_ne_zero k |>.symm
    | succ k =>
      cases j using Fin.cases with
      | zero =>
        simp [basisFuncND, refSimplexND, simplexND, h,
          MvPolynomial.eval_sum, Pi.single_apply]
      | succ l =>
        simp [basisFuncND, refSimplexND, simplexND, h,
          MvPolynomial.eval_sum, Pi.single_apply]

/-- Basis function is 1 at relevant vertex of reference simplex. -/
lemma basisNDIs1 :
    forall dim : Nat,
      basisFuncIs1AtVertex (refSimplexND dim) (basisFuncND dim) := by
  intro dim i
  simpa using basisNDEvalAtVertex dim i i

/-- Basis function is 0 at other vertices of reference simplex. -/
lemma basisNDIs0 :
    forall dim : Nat,
      basisFuncIs0AtOtherVertices (refSimplexND dim) (basisFuncND dim) := by
  intro dim i j hij
  simp only [bne_iff_ne] at hij
  simpa [hij] using basisNDEvalAtVertex dim i j

/-- Basis functions are square-integrable when bounded on any simplex. -/
lemma basisNDIsL2 :
    forall (dim : Nat) (s : Affine.Simplex Realish (Fin dim -> Realish) dim),
      basisFuncInL2 s (basisFuncND dim) := by
  intro dim s i

  let D : Set (Fin dim -> Real) := realDomainOfSimplex s
  let f : (Fin dim -> Real) -> Real :=
    fun x => MvPolynomial.eval x
      (MvPolynomial.map (algebraMap Realish Real) (basisFuncND dim i))

  have hD : IsCompact D := by
    dsimp [D, realDomainOfSimplex]
    exact (Set.finite_range
      (fun j : Fin (dim + 1) =>
        fun k : Fin dim => (s.points j k : Real))).isCompact_convexHull Real

  letI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict D) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hD.measure_ne_top

  have hf : Continuous f :=
    MvPolynomial.continuous_eval _

  cases hD.bddAbove_image hf.norm.continuousOn with
  | intro C hC =>
    have hbound :
        Filter.Eventually (fun x => norm (f x) <= C)
          (MeasureTheory.ae (MeasureTheory.volume.restrict D)) := by
      filter_upwards
        [MeasureTheory.self_mem_ae_restrict hD.isClosed.measurableSet]
        with x hx
      exact hC (Exists.intro x (And.intro hx rfl))

    exact MeasureTheory.MemLp.of_bound
      hf.aestronglyMeasurable C hbound
