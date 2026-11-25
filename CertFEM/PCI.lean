/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import Mathlib
import CertFEM.Util
import CertFEM.Simplex
import CertFEM.IRForm
import CertFEM.Quad

/-! # Proof-carrying integrators. -/

inductive IntegratorKind where
  | h1Coercive
  | l2Coercive
  | h1Skew
  | l2Skew  -- TODO: not provided
  | linear

abbrev AccumulatorOutput (dim : Nat) (kind : IntegratorKind) : Type :=
  match kind with
  | .linear => Fin (dim + 1) -> Real
  | _ => Fin (dim + 1) -> Fin (dim + 1) -> Real

def AccumulatorOutput.get {dim : Nat} {kind : IntegratorKind}
    (a : AccumulatorOutput dim kind)
    (i j : Fin (dim + 1)) : Real := by
  cases kind <;> first
    | exact a i
    | exact a i j

abbrev P1Basis (dim : Nat) :=
  Fin (dim + 1) -> MvPolynomial (Fin dim) Realish

noncomputable def basisAt {dim nq : Nat}
    (q : QuadScheme dim nq)
    (basis : P1Basis dim)
    (g : Fin nq)
    (i : Fin (dim + 1)) : Real :=
  MvPolynomial.eval
    (fun k => (q.pts g k : Real))
    (MvPolynomial.map (algebraMap Realish Real) (basis i))

noncomputable def gradAt {dim nq : Nat}
    (q : QuadScheme dim nq)
    (basis : P1Basis dim)
    (g : Fin nq)
    (i : Fin (dim + 1)) : Fin dim -> Real :=
  fun k =>
    MvPolynomial.eval
      (fun l => (q.pts g l : Real))
      (MvPolynomial.pderiv k
        (MvPolynomial.map (algebraMap Realish Real) (basis i)))

structure PCI (dim : Nat) where
  checkCoefficient : Realish -> Prop := fun _ => True
  checkExpr : ScalarExpr dim -> Prop := fun _ => True
  kind : IntegratorKind
  integrand :
    MvPolynomial (Fin dim) Realish ->
    MvPolynomial (Fin dim) Realish ->
    MvPolynomial (Fin dim) Realish
  accumulator {nq : Nat} :
    QuadScheme dim nq -> P1Basis dim -> (detJ : Real) -> AccumulatorOutput dim kind
  grammar : ScalarExpr dim

def PCI.refSimplex {dim : Nat}
    (pci : PCI dim) : Affine.Simplex Realish (Fin dim -> Realish) dim :=
  refSimplexND dim

abbrev PCI.realDomain {dim : Nat} (pci : PCI dim) : Set (Fin dim -> Real) :=
  realDomainOfSimplex pci.refSimplex

noncomputable def PCI.l2Norm {dim : Nat} (pci : PCI dim)
    (u : (Fin dim -> Real) -> Real) : Real :=
  MeasureTheory.lpNorm u 2
    (MeasureTheory.volume.restrict pci.realDomain)

noncomputable def partialDeriv {dim : Nat} (dir : Fin dim)
                  (v : (Fin dim -> Real) -> Real) : (Fin dim -> Real) -> Real :=
  fun x => fderiv Real v x (Pi.single dir 1)

noncomputable def PCI.h1Norm {dim : Nat} (pci : PCI dim)
    (u : (Fin dim -> Real) -> Real) : Real :=
  Real.sqrt (
    (pci.l2Norm u) ^ 2 +
    Finset.univ.sum (fun k : Fin dim =>
      (MeasureTheory.lpNorm (partialDeriv k u) 2
        (MeasureTheory.volume.restrict pci.realDomain)) ^ 2))

noncomputable def PCI.norm {dim : Nat} (pci : PCI dim)
                  (u : (Fin dim -> Real) -> Real) : Real :=
  match pci.kind with
  | .l2Coercive => pci.l2Norm u
  | .l2Skew => pci.l2Norm u
  | .linear => pci.l2Norm u
  | .h1Coercive => pci.h1Norm u
  | .h1Skew => pci.h1Norm u

noncomputable def PCI.integral {dim : Nat}
    (pci : PCI dim)
    (u v : MvPolynomial (Fin dim) Realish) : Real :=
  exactPolyIntegral (pci.integrand u v)

noncomputable def PCI.analyticIntegral {dim : PNat}
    (pci : PCI dim)
    (basis : Fin ((dim : Nat) + 1) -> MvPolynomial (Fin dim) Realish)
    (i j : Fin ((dim : Nat) + 1)) : Real :=
  MeasureTheory.integral
    (MeasureTheory.volume.restrict
      (realDomainOfSimplex (refSimplexND dim)))
    (fun x => evalPoly (pci.integrand (basis i) (basis j)) x)

/-! ## PCI equivalence -/

def formEqIntegrand {dim : Nat} (pci : PCI dim) : Prop :=
  forall
    (basis : Fin (dim + 1) -> MvPolynomial (Fin dim) Realish)
    (i j : Fin (dim + 1)),
    pci.grammar.denote basis i j =
      pci.integrand (basis i) (basis j)

def accEqIntegral {dim : Nat} (pci : PCI dim) : Prop :=
  forall
    (basis : P1Basis dim)
    (i j : Fin (dim + 1))
    (nq maxDegree : Nat)
    (q : QuadScheme dim nq),
    QuadExact q maxDegree ->
    (pci.integrand (basis i) (basis j)).totalDegree <= maxDegree ->
    pci.integral (basis i) (basis j) =
      AccumulatorOutput.get (pci.accumulator q basis 1) i j

lemma accEqIntegral_of_eval
    {dim : Nat} (pci : PCI dim)
    (h : forall
      (basis : P1Basis dim)
      (i j : Fin (dim + 1))
      (nq : Nat)
      (q : QuadScheme dim nq),
      AccumulatorOutput.get (pci.accumulator q basis 1) i j =
        quadSum q 1 (fun g =>
          evalPoly (pci.integrand (basis i) (basis j)) (q.pts g))) :
    accEqIntegral pci := by
  intro basis i j nq maxDegree q hExact hDegree
  change exactPolyIntegral
    (pci.integrand (basis i) (basis j)) =
      AccumulatorOutput.get (pci.accumulator q basis 1) i j
  calc
    exactPolyIntegral (pci.integrand (basis i) (basis j)) =
        quadSum q 1 (fun g =>
          evalPoly (pci.integrand (basis i) (basis j)) (q.pts g)) :=
      (hExact _ hDegree).symm
    _ = _ := (h basis i j nq q).symm

theorem exactPolyIntegral_of_moments
    {dim : Nat}
    (s : Set (Fin dim -> Real))
    (hInt : forall m : Finsupp (Fin dim) Nat,
      MeasureTheory.Integrable
        (fun x : Fin dim -> Real =>
          Finset.univ.prod (fun k : Fin dim => x k ^ m k))
        (MeasureTheory.volume.restrict s))
    (hMoment : forall m : Finsupp (Fin dim) Nat,
      MeasureTheory.integral
        (MeasureTheory.volume.restrict s)
        (fun x : Fin dim -> Real =>
          Finset.univ.prod (fun k : Fin dim => x k ^ m k))
        = referenceMoment m)
    (p : MvPolynomial (Fin dim) Realish) :
    exactPolyIntegral p =
      MeasureTheory.integral
        (MeasureTheory.volume.restrict s)
        (fun x => evalPoly p x) := by
  classical

  let mu : MeasureTheory.Measure (Fin dim -> Real) :=
    MeasureTheory.volume.restrict s

  have hEval (x : Fin dim -> Real) :
      evalPoly p x =
        p.support.sum (fun m =>
          algebraMap Realish Real (MvPolynomial.coeff m p) *
            Finset.univ.prod (fun k : Fin dim => x k ^ m k)) := by
    unfold evalPoly
    rw [MvPolynomial.eval_eq',
      MvPolynomial.support_map_of_injective p (algebraMap Realish Real).injective]
    simp only [MvPolynomial.coeff_map]

  calc
    exactPolyIntegral p =
        p.support.sum (fun m =>
          algebraMap Realish Real (MvPolynomial.coeff m p) *
            referenceMoment m) := rfl
    _ = p.support.sum (fun m =>
          MeasureTheory.integral mu (fun x =>
            algebraMap Realish Real (MvPolynomial.coeff m p) *
              Finset.univ.prod (fun k : Fin dim => x k ^ m k))) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [MeasureTheory.integral_const_mul, hMoment m]
    _ = MeasureTheory.integral mu (fun x =>
          p.support.sum (fun m =>
            algebraMap Realish Real (MvPolynomial.coeff m p) *
              Finset.univ.prod (fun k : Fin dim => x k ^ m k))) := by
        symm
        apply MeasureTheory.integral_finsetSum
        intro m hm
        exact (hInt m).const_mul _
    _ = MeasureTheory.integral mu (fun x => evalPoly p x) := by
        rw [show
          (fun x : Fin dim -> Real => evalPoly p x) =
          (fun x : Fin dim -> Real =>
            p.support.sum (fun m =>
              algebraMap Realish Real (MvPolynomial.coeff m p) *
                Finset.univ.prod (fun k : Fin dim => x k ^ m k))
          ) from funext hEval]

lemma PCI.l2Norm_le_h1Norm {dim : Nat}
    (pci : PCI dim)
    (u : (Fin dim -> Real) -> Real) :
    pci.l2Norm u <= pci.h1Norm u := by
  unfold PCI.h1Norm
  apply Real.le_sqrt_of_sq_le
  have hs : 0 <= Finset.univ.sum (fun k : Fin dim =>
      (MeasureTheory.lpNorm (partialDeriv k u) 2
        (MeasureTheory.volume.restrict pci.realDomain)) ^ 2) := by
    apply Finset.sum_nonneg
    intro k hk
    positivity
  linarith

lemma PCI.derivL2_le_h1Norm {dim : Nat}
    (pci : PCI dim)
    (u : (Fin dim -> Real) -> Real)
    (dir : Fin dim) :
    MeasureTheory.lpNorm (partialDeriv dir u) 2
      (MeasureTheory.volume.restrict pci.realDomain) <=
        pci.h1Norm u := by
  unfold PCI.h1Norm
  apply Real.le_sqrt_of_sq_le

  have hs :
      (MeasureTheory.lpNorm (partialDeriv dir u) 2
        (MeasureTheory.volume.restrict pci.realDomain)) ^ 2 <=
      Finset.univ.sum (fun k : Fin dim =>
        (MeasureTheory.lpNorm (partialDeriv k u) 2
          (MeasureTheory.volume.restrict pci.realDomain)) ^ 2) := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin dim)))
      (f := fun k : Fin dim =>
        (MeasureTheory.lpNorm (partialDeriv k u) 2
          (MeasureTheory.volume.restrict pci.realDomain)) ^ 2)
      (by
        intro k hk
        positivity)
      (Finset.mem_univ dir)

  nlinarith [sq_nonneg (pci.l2Norm u)]
