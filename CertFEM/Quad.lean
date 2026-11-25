/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import Mathlib
import CertFEM.Util

/-! # Gauss-Legendre Quadrature -/

structure QuadScheme (dim nq : Nat) where
  pts : Fin nq -> Fin dim -> Real
  wts : Fin nq -> Real

/-- Definition 5.8 (Quadrature roots). -/
def QuadScheme.HasLegendreRoots {nq : Nat}
    (q : QuadScheme 1 nq) : Prop :=
  forall g : Fin nq,
    Polynomial.aeval ((q.pts g 0 + 1) / 2) -- shift back to regular range
      (Polynomial.shiftedLegendre nq) = 0

/-- Definition 5.9 (Quadrature weights). -/
def QuadScheme.HasExactMoments {nq : Nat}
    (q : QuadScheme 1 nq) : Prop :=
  forall k : Fin (2 * nq),
    Finset.univ.sum (fun g : Fin nq =>
      q.wts g * (q.pts g 0) ^ k.val) =
    intervalIntegral
      (fun x : Real => x ^ k.val)
      (-1 : Real) (1 : Real) MeasureTheory.volume

noncomputable def quadSum {dim nq : Nat}
    (q : QuadScheme dim nq)
    (detJ : Real)
    (f : Fin nq -> Real) : Real :=
  Finset.univ.sum (fun g : Fin nq =>
    detJ * (q.wts g : Real) * f g)

noncomputable def referenceMoment {dim : Nat}
    (m : Finsupp (Fin dim) Nat) : Real :=
  let degree : Nat := m.sum (fun _ n => n)
  if (dim : Nat) = 1 then
    if degree % 2 = 0 then
      (2 : Real) / ((degree : Real) + 1)
    else
      0
  else
    (Finset.univ.prod (fun k : Fin dim =>
      (Nat.factorial (m k) : Real))) /
    (Nat.factorial ((dim : Nat) + degree) : Real)

noncomputable def exactPolyIntegral {dim : Nat}
    (p : MvPolynomial (Fin dim) Realish) : Real := by
  classical
  exact p.support.sum (fun m =>
    algebraMap Realish Real (MvPolynomial.coeff m p) *
      referenceMoment (dim := dim) m)

noncomputable def evalPoly {dim : Nat}
    (p : MvPolynomial (Fin dim) Realish)
    (x : Fin dim -> Real) : Real :=
  MvPolynomial.eval x
    (MvPolynomial.map (algebraMap Realish Real) p)

def QuadExact {dim nq : Nat}
    (q : QuadScheme dim nq) (maxDegree : Nat) : Prop :=
  forall p : MvPolynomial (Fin dim) Realish,
    p.totalDegree <= maxDegree ->
      quadSum q 1
        (fun g => evalPoly p (fun k => (q.pts g k : Real))) =
      exactPolyIntegral p

def QuadScheme.HasExactMomentsDiscrete {nq : Nat}
    (q : QuadScheme 1 nq) : Prop :=
  forall k : Fin (2 * nq),
    Finset.univ.sum (fun g : Fin nq =>
      q.wts g * (q.pts g 0) ^ k.val) =
    ((1 : Real) - (-1 : Real) ^ (k.val + 1)) /
      (k.val + 1)

def QuadScheme.IsGaussLegendre {nq : Nat} (q : QuadScheme 1 nq) : Prop :=
  q.HasLegendreRoots /\ q.HasExactMomentsDiscrete

lemma QuadScheme.Discretize {nq : Nat} (q : QuadScheme 1 nq) :
    q.HasExactMomentsDiscrete -> q.HasExactMoments := by
  intro h k
  rw [h k]
  simpa using
    (intervalIntegral.integral_pow
      (a := (-1 : Real)) (b := (1 : Real)) k.val).symm

/-! ## Included Quadrature schemes -/

noncomputable def threePtQuad : QuadScheme 1 3 :=
  { pts := fun g _ =>
      ![-((3 : Real) / 5).sqrt,
        0,
        ((3 : Real) / 5).sqrt] g
    wts := ![5 / 9, 8 / 9, 5 / 9] }

private lemma threePtMoments : threePtQuad.HasExactMomentsDiscrete := by
  intro k

  have h2 : ((3 : Real) / 5).sqrt ^ 2 = (3 : Real) / 5 := by
    rw [Real.sq_sqrt (by norm_num)]

  have h4 : ((3 : Real) / 5).sqrt ^ 4 = (9 : Real) / 25 := by
    calc
      _ = (((3 : Real) / 5).sqrt ^ 2) ^ 2 := by ring
      _ = _ := by rw [h2]; norm_num

  fin_cases k <;>
    simp [threePtQuad, Fin.sum_univ_succ] <;>
    ring_nf <;>
  all_goals
    have h3 : (Real.sqrt (3 : Real)) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    have h5 : (Real.sqrt (5 : Real)) ^ 2 = 5 :=
      Real.sq_sqrt (by norm_num)

    have h34 : (Real.sqrt (3 : Real)) ^ 4 = 9 := by
      calc
        _ = ((Real.sqrt (3 : Real)) ^ 2) ^ 2 := by ring
        _ = 9 := by rw [h3]; norm_num

    have h54 : (Real.sqrt (5 : Real)) ^ 4 = 25 := by
      calc
        _ = ((Real.sqrt (5 : Real)) ^ 2) ^ 2 := by ring
        _ = 25 := by rw [h5]; norm_num

    simp only [inv_pow, h3, h5, h34, h54]
    norm_num

private lemma shiftedLegendre3_eval (x : Real) :
    Polynomial.aeval x (Polynomial.shiftedLegendre 3) =
      1 - 12 * x + 30 * x ^ 2 - 20 * x ^ 3 := by
  simp [Polynomial.shiftedLegendre, Finset.sum_range_succ]

  have h3 :
      Polynomial.aeval x (3 : Polynomial Int) = (3 : Real) := by
    exact Polynomial.aeval_natCast x 3

  have h4 :
      Polynomial.aeval x (4 : Polynomial Int) = (4 : Real) := by
    exact Polynomial.aeval_natCast x 4

  rw [h3, h4]
  norm_num [Nat.choose] <;> ring

private lemma shiftedLegendre3_root (t : Real)
    (ht : t = 0 \/ t ^ 2 = (3 : Real) / 5) :
    Polynomial.aeval ((t + 1) / 2)
      (Polynomial.shiftedLegendre 3) = 0 := by
  rw [shiftedLegendre3_eval]
  calc
    1 - 12 * ((t + 1) / 2) +
      30 * ((t + 1) / 2) ^ 2 -
      20 * ((t + 1) / 2) ^ 3 =
        t * (3 - 5 * t ^ 2) / 2 := by ring
    _ = 0 := by
      rcases ht with hzero | hsquare
      next =>
        subst t
        norm_num
      next =>
        rw [hsquare]
        norm_num

private lemma threePtRoots :
    threePtQuad.HasLegendreRoots := by
  intro g

  have hs : ((3 : Real) / 5).sqrt ^ 2 =
      (3 : Real) / 5 := by
    rw [Real.sq_sqrt (by norm_num)]

  fin_cases g

  all_goals
    first
    | simpa [threePtQuad] using
        (shiftedLegendre3_root (-((3 : Real) / 5).sqrt)
          (Or.inr (by nlinarith [hs])))
    | simpa [threePtQuad] using
        (shiftedLegendre3_root 0 (Or.inl rfl))
    | simpa [threePtQuad] using
        (shiftedLegendre3_root (((3 : Real) / 5).sqrt)
          (Or.inr hs))

theorem threePtIsGauss : threePtQuad.IsGaussLegendre := by
  exact And.intro threePtRoots threePtMoments

structure RatQuadScheme (dim nq : Nat) where
  pts : Fin nq -> Fin dim -> Realish
  wts : Fin nq -> Realish

noncomputable def rationalizeQuad {dim nq : Nat}
    (q : QuadScheme dim nq)
    (tol : Real)
    (htol : 0 < tol) : RatQuadScheme dim nq :=
  { pts := fun g k =>
      Classical.choose (exists_rat_near (q.pts g k) htol)
    wts := fun g =>
      Classical.choose (exists_rat_near (q.wts g) htol) }

theorem rationalizeQuad_pts_close {dim nq : Nat}
    (q : QuadScheme dim nq)
    (tol : Real)
    (htol : 0 < tol)
    (g : Fin nq)
    (k : Fin dim) :
    |q.pts g k - ((rationalizeQuad q tol htol).pts g k : Real)| < tol := by
  exact Classical.choose_spec (exists_rat_near (q.pts g k) htol)

theorem rationalizeQuad_wts_close {dim nq : Nat}
    (q : QuadScheme dim nq)
    (tol : Real)
    (htol : 0 < tol)
    (g : Fin nq) :
    |q.wts g - ((rationalizeQuad q tol htol).wts g : Real)| < tol := by
  exact Classical.choose_spec (exists_rat_near (q.wts g) htol)

def QuadMomentExact {dim nq : Nat}
    (q : QuadScheme dim nq)
    (maxDegree : Nat) : Prop :=
  forall m : Finsupp (Fin dim) Nat,
    m.sum (fun _ n => n) <= maxDegree ->
      quadSum q 1 (fun g =>
        Finset.univ.prod (fun k : Fin dim =>
          (q.pts g k : Real) ^ m k)) =
      referenceMoment m

private lemma threePtMomentExact : QuadMomentExact threePtQuad 5 := by
  intro m hm

  have hdegree :
      m.sum (fun _ n => n) = m 0 := by
    rw [Finsupp.sum_fintype m (fun _ n => n) (by simp)]
    simp [Fin.sum_univ_succ]

  have hk : m 0 < 6 := by
    omega

  have hRef :
      referenceMoment m =
        ((1 : Real) - (-1 : Real) ^ (m 0 + 1)) /
          (m 0 + 1) := by
    interval_cases hd : m 0 <;>
      simp [referenceMoment, hdegree, hd] <;>
      norm_num

  calc
    quadSum threePtQuad 1
        (fun g =>
          Finset.univ.prod (fun k : Fin 1 =>
            threePtQuad.pts g k ^ m k)) =
        Finset.univ.sum (fun g : Fin 3 =>
          threePtQuad.wts g *
            threePtQuad.pts g 0 ^ m 0) := by
      simp [quadSum, Fin.prod_univ_succ]
    _ = ((1 : Real) - (-1 : Real) ^ (m 0 + 1)) /
          (m 0 + 1) := by
      simpa using
        (threePtMoments (Fin.mk (m 0) hk : Fin 6))
    _ = referenceMoment m := hRef.symm

theorem quadExact_of_moments
    {dim nq : Nat}
    (q : QuadScheme dim nq)
    (maxDegree : Nat)
    (h : QuadMomentExact q maxDegree) :
    QuadExact q maxDegree := by
  classical
  intro p hp

  let c (m : Finsupp (Fin dim) Nat) : Real :=
    algebraMap Realish Real (MvPolynomial.coeff m p)

  let mon (m : Finsupp (Fin dim) Nat) (g : Fin nq) : Real :=
    Finset.univ.prod (fun k : Fin dim => q.pts g k ^ m k)

  have hEval (g : Fin nq) :
      evalPoly p (q.pts g) =
        p.support.sum (fun m => c m * mon m g) := by
    dsimp [evalPoly, c, mon]
    rw [MvPolynomial.eval_eq',
      MvPolynomial.support_map_of_injective p (algebraMap Realish Real).injective]
    simp only [MvPolynomial.coeff_map]

  have hMoment (m : Finsupp (Fin dim) Nat)
      (hm : Membership.mem p.support m) :
      Finset.univ.sum (fun g : Fin nq =>
        q.wts g * mon m g) = referenceMoment m := by
    have hDegree :
        m.sum (fun _ n => n) <= maxDegree :=
      (MvPolynomial.le_totalDegree hm).trans hp
    simpa [QuadMomentExact, quadSum, mon] using
      h m hDegree

  calc
    quadSum q 1 (fun g => evalPoly p (q.pts g)) =
        Finset.univ.sum (fun g : Fin nq =>
          q.wts g *
            p.support.sum (fun m => c m * mon m g)) := by
      simp only [quadSum, one_mul]
      apply Finset.sum_congr rfl
      intro g _
      rw [hEval g]
    _ = Finset.univ.sum (fun g : Fin nq =>
          p.support.sum (fun m =>
            c m * (q.wts g * mon m g))) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = p.support.sum (fun m =>
          Finset.univ.sum (fun g : Fin nq =>
            c m * (q.wts g * mon m g))) := by
      rw [Finset.sum_comm]
    _ = p.support.sum (fun m =>
          c m * Finset.univ.sum (fun g : Fin nq =>
            q.wts g * mon m g)) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
    _ = p.support.sum (fun m =>
          c m * referenceMoment m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hMoment m hm]
    _ = exactPolyIntegral p := rfl

lemma ThreePtExact : QuadExact threePtQuad 5 := by
  exact quadExact_of_moments
    threePtQuad 5 threePtMomentExact
