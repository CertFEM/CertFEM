/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.Util
import CertFEM.Quad

/-! # Duffy transform -/

/-- Transform a quadrature scheme as per Equation 3 and Equation 4. -/
noncomputable def duffyTransform {nq : Nat}
    (q : QuadScheme 1 nq)
    (dim : Nat) : QuadScheme dim (nq ^ dim) where
  pts := fun g k =>
    let idx := finFunctionFinEquiv.symm g
    let t := fun i => q.pts (idx i) 0
    ((1 + t k) / 2) *
      ((Finset.univ.filter (fun l : Fin dim => k < l)).prod
        (fun l => (1 - t l) / 2))

  wts := fun g =>
    let idx := finFunctionFinEquiv.symm g
    (Finset.univ : Finset (Fin dim)).prod
      (fun k =>
        (q.wts (idx k) / 2) *
          ((1 - q.pts (idx k) 0) / 2) ^ k.val)

/-! ## Duffy exactness -/

private lemma duffyPt0 (a b : Fin 3) :
    (duffyTransform threePtQuad 2).pts
      (finFunctionFinEquiv (![a, b] : Fin 2 -> Fin 3)) 0 =
    ((1 + threePtQuad.pts a 0) / 2) *
      ((1 - threePtQuad.pts b 0) / 2) := by
  have hf0 :
      (Finset.univ.filter
        (fun l : Fin 2 => (0 : Fin 2) < l)) =
        ({1} : Finset (Fin 2)) := by
    decide
  simp [duffyTransform, hf0]

private lemma duffyPt1 (a b : Fin 3) :
    (duffyTransform threePtQuad 2).pts
      (finFunctionFinEquiv (![a, b] : Fin 2 -> Fin 3)) 1 =
    (1 + threePtQuad.pts b 0) / 2 := by
  have hf1 :
      (Finset.univ.filter
        (fun l : Fin 2 => (1 : Fin 2) < l)) =
        (Finset.empty : Finset (Fin 2)) := by
    decide

  have hprod :
      (Finset.univ.filter
        (fun l : Fin 2 => (1 : Fin 2) < l)).prod
          (fun l => 1 - threePtQuad.pts (![a, b] l) 0) = 1 := by
    rw [hf1]
    exact Finset.prod_empty

  have hcard :
      (Finset.univ.filter
        (fun l : Fin 2 => (1 : Fin 2) < l)).card = 0 := by
    rw [hf1]
    exact Finset.card_empty

  simp [duffyTransform, hprod, hcard]

private lemma duffyWts (a b : Fin 3) :
    (duffyTransform threePtQuad 2).wts
      (finFunctionFinEquiv (![a, b] : Fin 2 -> Fin 3)) =
    (threePtQuad.wts a / 2) *
      (threePtQuad.wts b / 2) *
      ((1 - threePtQuad.pts b 0) / 2) := by
  simp [duffyTransform, Fin.prod_univ_two] <;>
    ring

private lemma duffyTerm
    (a b : Fin 3) (m : Finsupp (Fin 2) Nat) :
    (duffyTransform threePtQuad 2).wts
        (finFunctionFinEquiv (![a, b])) *
      (Finset.univ.prod (fun k : Fin 2 =>
        (duffyTransform threePtQuad 2).pts
          (finFunctionFinEquiv (![a, b])) k ^ m k)) =
    ((threePtQuad.wts a / 2) *
      (threePtQuad.wts b / 2) *
      ((1 - threePtQuad.pts b 0) / 2)) *
    (((1 + threePtQuad.pts a 0) / 2 *
      ((1 - threePtQuad.pts b 0) / 2)) ^ m 0 *
      ((1 + threePtQuad.pts b 0) / 2) ^ m 1) := by
  rw [Fin.prod_univ_two]
  rw [duffyWts, duffyPt0, duffyPt1]

private lemma duffySumReindex (f : Fin (3 ^ 2) -> Real) :
    Finset.univ.sum (fun g : Fin (3 ^ 2) => f g) =
      Finset.univ.sum (fun a : Fin 3 =>
        Finset.univ.sum (fun b : Fin 3 =>
          f (finFunctionFinEquiv
            (![a, b] : Fin 2 -> Fin 3)))) := by
  let e : Equiv (Prod (Fin 3) (Fin 3)) (Fin (3 ^ 2)) :=
    (finTwoArrowEquiv (Fin 3)).symm.trans finFunctionFinEquiv
  calc
    _ = Finset.univ.sum
          (fun ab : Prod (Fin 3) (Fin 3) => f (e ab)) :=
      (Equiv.sum_comp e f).symm
    _ = _ := by
      simp [Fintype.sum_prod_type, e, finTwoArrowEquiv_symm_apply]

private lemma duffyMomentExact2 :
        QuadMomentExact (duffyTransform threePtQuad 2) 2 := by
  intro m hm

  have hdeg :
      m.sum (fun _ n => n) = m 0 + m 1 := by
    rw [Finsupp.sum_fintype m (fun _ n => n) (by simp)]
    simp [Fin.sum_univ_succ]

  have hab : m 0 + m 1 <= 2 := by omega
  have ha : m 0 <= 2 := by omega
  have hb : m 1 <= 2 := by omega

  have href :
      referenceMoment m =
        ((Nat.factorial (m 0) : Real) *
          (Nat.factorial (m 1) : Real)) /
          (Nat.factorial (2 + m 0 + m 1) : Real) := by
    simp [referenceMoment, hdeg, Fin.prod_univ_two,
      Nat.add_assoc]

  rw [href]
  simp only [quadSum, one_mul]
  rw [duffySumReindex]
  simp_rw [duffyTerm]

  dsimp only [threePtQuad]
  generalize hs : ((3 : Real) / 5).sqrt = r at *

  have hr2 : r ^ 2 = (3 : Real) / 5 := by
    have hh : ((3 : Real) / 5).sqrt ^ 2 =
        (3 : Real) / 5 := Real.sq_sqrt (by norm_num)
    simpa only [hs] using hh

  have hr4 : r ^ 4 = (9 : Real) / 25 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = (9 : Real) / 25 := by rw [hr2]; norm_num

  interval_cases h0 : m 0 <;>
    interval_cases h1 : m 1

  all_goals try omega

  all_goals
    simp [Fin.sum_univ_succ] <;>
    ring_nf <;>
    nlinarith [hr2, hr4]

/-- Duffy transform is exact in 2D for polynomials up to degree 2.

It's exact to degree 4, but we prove the weaker case to avoid state explosion.
-/
lemma DuffyExact2D2 : QuadExact (duffyTransform threePtQuad 2) 2 := by
  exact quadExact_of_moments
    (duffyTransform threePtQuad 2) 2 duffyMomentExact2
