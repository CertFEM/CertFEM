/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.Quad
import Mathlib.Data.Rat.NatSqrt.Real

/-! # Tolerance-controlled conversion between exact and rational quadrature. -/

/-- Embed a rational quadrature rule into the exact real semantics. -/
def RatQuadScheme.toReal {dim nq : Nat} (q : RatQuadScheme dim nq) : QuadScheme dim nq :=
  { pts := fun g k => (q.pts g k : Real), wts := fun g => (q.wts g : Real) }

/-- The representation-conversion contract; tolerances bound absolute errors. -/
def QuadratureClose {dim nq : Nat} (exact : QuadScheme dim nq)
    (approx : RatQuadScheme dim nq) (tol : Real) : Prop :=
  (forall g k, |exact.pts g k - (approx.pts g k : Real)| < tol) /\
    (forall g, |exact.wts g - (approx.wts g : Real)| < tol)

/-- Arbitrary exact real rules have rational approximations at every positive tolerance.
This existence-based conversion is noncomputable; the Gauss rule below has executable conversion. -/
theorem rationalizeQuad_close {dim nq : Nat} (q : QuadScheme dim nq)
    (tol : Real) (htol : 0 < tol) : QuadratureClose q (rationalizeQuad q tol htol) tol :=
  And.intro (rationalizeQuad_pts_close q tol htol) (rationalizeQuad_wts_close q tol htol)

/-- Executable square-root approximation. Positive rational tolerance selects an integer
precision large enough to bound the absolute error; no floating-point constants are used. -/
def approximateNatSqrt (x : Nat) (tol : Realish) : Realish := Nat.ratSqrt x tol.den

private lemma inverse_den_le (tol : Realish) (htol : 0 < tol) :
    (1 : Real) / tol.den <= (tol : Real) := by
  have hp : 0 < tol.num := Rat.num_pos.mpr htol
  have hn : (1 : Int) <= tol.num := by omega
  have hreal : (1 : Real) <= (tol.num : Real) := by exact_mod_cast hn
  rw [Rat.cast_def]
  exact div_le_div_of_nonneg_right hreal (by positivity)

/-- The executable approximation satisfies the requested absolute tolerance. -/
theorem approximateNatSqrt_close (x : Nat) (tol : Realish) (htol : 0 < tol) :
    |Real.sqrt (x : Real) - (approximateNatSqrt x tol : Real)| < (tol : Real) := by
  unfold approximateNatSqrt
  have hprec := tol.den_pos
  rw [abs_of_nonneg (sub_nonneg.mpr (Nat.ratSqrt_le_realSqrt x hprec))]
  have h := Nat.realSqrt_lt_ratSqrt_add_inv_prec x hprec
  have ht := inverse_den_le tol htol
  linarith

/-- Executable three-point Gauss rule with exact rational weights and approximated nodes. -/
def approximateThreePt (tol : Realish) : RatQuadScheme 1 3 where
  pts g _ := ![-(approximateNatSqrt 15 tol / 5), 0, approximateNatSqrt 15 tol / 5] g
  wts := ![5 / 9, 8 / 9, 5 / 9]

private lemma gauss_root_rescale : Real.sqrt ((3 : Real) / 5) = Real.sqrt 15 / 5 := by
  have ha := Real.sq_sqrt (show (0 : Real) <= 15 by norm_num)
  have hb := Real.sq_sqrt (show (0 : Real) <= 3 / 5 by norm_num)
  nlinarith [Real.sqrt_nonneg (15 : Real), Real.sqrt_nonneg ((3 : Real) / 5)]

/-- The actual rational Gauss rule used by the compiler meets its tolerance contract. -/
theorem approximateThreePt_close (tol : Realish) (htol : 0 < tol) :
    QuadratureClose threePtQuad (approximateThreePt tol) tol := by
  have hp : (0 : Real) < tol := by exact_mod_cast htol
  have h := approximateNatSqrt_close 15 tol htol
  norm_num only [Nat.cast_ofNat] at h
  have hb : |Real.sqrt 15 / 5 - (approximateNatSqrt 15 tol : Real) / 5| < (tol : Real) := by
    rw [<- sub_div, abs_div]
    norm_num
    linarith
  constructor
  . intro g k
    fin_cases g
    . change |-(Real.sqrt ((3 : Real) / 5)) - (-(approximateNatSqrt 15 tol / 5) : Realish)| < _
      push_cast
      rw [gauss_root_rescale, neg_sub_neg, abs_sub_comm]
      exact hb
    . change |(0 : Real) - (0 : Realish)| < _
      simpa only [Rat.cast_zero, sub_self, abs_zero] using hp
    . change |Real.sqrt ((3 : Real) / 5) - (approximateNatSqrt 15 tol / 5 : Realish)| < _
      push_cast
      rw [gauss_root_rescale]
      exact hb
  . intro g
    fin_cases g <;> norm_num [threePtQuad, approximateThreePt, hp]

/-- Multiplication error splits into input-value and coefficient errors. -/
lemma product_error (w v f h : Real) :
    |w * f - v * h| <= |w| * |f - h| + |w - v| * |h| := by
  calc
    |w * f - v * h| = |w * (f - h) + (w - v) * h| := by congr 1; ring
    _ <= |w * (f - h)| + |(w - v) * h| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]

/-- Approximation errors propagate through quadrature accumulation, including arbitrary
Jacobian scaling. This states a bound, rather than identifying rounded and exact rules. -/
theorem quadSum_error {dim nq : Nat} (q r : QuadScheme dim nq)
    (detJ : Real) (f h : Fin nq -> Real) :
    |quadSum q detJ f - quadSum r detJ h| <= |detJ| *
      Finset.univ.sum (fun g => |q.wts g| * |f g - h g| + |q.wts g - r.wts g| * |h g|) := by
  unfold quadSum
  rw [<- Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro g _
  calc
    |detJ * q.wts g * f g - detJ * r.wts g * h g| =
        |detJ| * |q.wts g * f g - r.wts g * h g| := by rw [<- abs_mul]; congr 1; ring
    _ <= _ := mul_le_mul_of_nonneg_left (product_error _ _ _ _) (abs_nonneg _)

/-- A user-supplied sample error bound combines with the representation tolerance.
A bound on sample errors can, for example, be obtained from the integrand's Lipschitz constant. -/
theorem quadSum_error_of_close {dim nq : Nat} (q : QuadScheme dim nq)
    (r : RatQuadScheme dim nq) (tol eps : Real) (hc : QuadratureClose q r tol)
    (f h : Fin nq -> Real) (hf : forall g, |f g - h g| <= eps) (detJ : Real) :
    |quadSum q detJ f - quadSum r.toReal detJ h| <=
      |detJ| * Finset.univ.sum (fun g => |q.wts g| * eps + tol * |h g|) := by
  apply (quadSum_error q r.toReal detJ f h).trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Finset.sum_le_sum
  intro g _
  exact add_le_add (mul_le_mul_of_nonneg_left (hf g) (abs_nonneg _))
    (mul_le_mul_of_nonneg_right (hc.2 g).le (abs_nonneg _))
