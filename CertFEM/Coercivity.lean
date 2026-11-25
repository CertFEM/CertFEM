/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.Boundedness
import CertFEM.PCI
import CertFEM.DefPCI

/-! # Coercivity proofs

The main point of interest here is `TopLevel.Valid`.

## Coercivity on an explicitly specified zero-boundary space (Section 6.2).
-/

namespace Variational

/-- The explicit H1_0 interface used by the paper's coercivity proof.
Poincare and integration by parts are hypotheses on this space, not axioms or
claims about an arbitrary element-local polynomial basis. -/
structure ZeroBoundarySpace (dim : Nat) extends Space dim where
  poincareConstant : Real
  poincare : forall u, admissible u ->
    toSpace.l2 u ^ 2 <= poincareConstant ^ 2 * toSpace.energy u
  integrationByParts : forall u, admissible u -> forall v, admissible v -> forall k,
    toSpace.gradient k u v = -toSpace.gradient k v u

namespace Space

variable {dim : Nat} (s : Space dim)

lemma l2_sq_integral {X : Type*} [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    (u : X -> Real) (hu : MeasureTheory.MemLp u 2 mu) :
    MeasureTheory.lpNorm u 2 mu ^ 2 = MeasureTheory.integral mu (fun x => u x * u x) := by
  have h : MeasureTheory.lpNorm u 2 mu =
      Real.sqrt (MeasureTheory.integral mu (fun x => u x * u x)) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hu.aestronglyMeasurable]
    norm_num [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs, <- sq]
  rw [h, Real.sq_sqrt]
  exact MeasureTheory.integral_nonneg fun x => mul_self_nonneg _

lemma diffusion_self (u : FunctionSpace dim) (hu : s.admissible u) :
    s.diffusion u u = s.energy u := by
  apply Finset.sum_congr rfl
  intro k _
  exact (l2_sq_integral s.measure _ (s.derivMemLp u hu k)).symm

lemma mass_self_nonneg (u : FunctionSpace dim) : 0 <= s.mass u u :=
  MeasureTheory.integral_nonneg fun x => mul_self_nonneg _

/-- A uniform lower bound on the symmetric part of a constant diffusion tensor. -/
def UniformElliptic (D : Matrix (Fin dim) (Fin dim) Real) (alpha : Real) : Prop :=
  forall z : Fin dim -> Real,
    alpha * Finset.univ.sum (fun k => z k * z k) <=
      Finset.univ.sum (fun k => Finset.univ.sum fun l => D k l * (z k * z l))

/-- Pointwise ellipticity gives an energy lower bound after integration. -/
theorem anisotropic_energy (D : Matrix (Fin dim) (Fin dim) Real) (alpha : Real)
    (hD : UniformElliptic D alpha) (u : FunctionSpace dim) (hu : s.admissible u) :
    alpha * s.energy u <= s.anisotropic D u u := by
  have hint (k l : Fin dim) : MeasureTheory.Integrable
      (fun x => partialDeriv k u x * partialDeriv l u x) s.measure :=
    (s.derivMemLp u hu k).integrable_mul (s.derivMemLp u hu l)
  have he : s.energy u = MeasureTheory.integral s.measure (fun x =>
      Finset.univ.sum fun k => partialDeriv k u x * partialDeriv k u x) := by
    rw [<- s.diffusion_self u hu]
    exact (MeasureTheory.integral_finsetSum _ (fun k _ => hint k k)).symm
  have hsum (k : Fin dim) : MeasureTheory.Integrable
      (fun x => Finset.univ.sum fun l => D k l *
        (partialDeriv k u x * partialDeriv l u x)) s.measure :=
    MeasureTheory.integrable_finsetSum _ fun l _ => (hint k l).const_mul _
  have ha : s.anisotropic D u u = MeasureTheory.integral s.measure (fun x =>
      Finset.univ.sum fun k => Finset.univ.sum fun l => D k l *
        (partialDeriv k u x * partialDeriv l u x)) := by
    rw [MeasureTheory.integral_finsetSum _ (fun k _ => hsum k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [MeasureTheory.integral_finsetSum _ (fun l _ => (hint k l).const_mul _)]
    simp only [anisotropic, MeasureTheory.integral_const_mul]
  rw [he, ha, <- MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_mono
  . exact (MeasureTheory.integrable_finsetSum _ (fun k _ => hint k k)).const_mul _
  . exact MeasureTheory.integrable_finsetSum _ fun k _ => hsum k
  . intro x
    exact hD (fun k => partialDeriv k u x)

end Space

namespace ZeroBoundarySpace

variable {dim : Nat} (s : ZeroBoundarySpace dim)

noncomputable def coercivityConstant : Real := 1 / (s.poincareConstant ^ 2 + 1)

lemma coercivityConstant_pos : 0 < s.coercivityConstant := by
  unfold coercivityConstant
  positivity

/-- Paper theorem "Proof-carrying integrator coercivity", diffusion base case.
The Poincare constant is retained explicitly as 1 / (C_P^2 + 1). -/
theorem diffusion_coercive (u : FunctionSpace dim) (hu : s.admissible u) :
    s.coercivityConstant * s.h1 u ^ 2 <= s.diffusion u u := by
  rw [s.toSpace.diffusion_self u hu]
  have h := s.poincare u hu
  rw [s.toSpace.h1_sq]
  unfold coercivityConstant
  have hp : 0 < s.poincareConstant ^ 2 + 1 := by positivity
  calc
    1 / (s.poincareConstant ^ 2 + 1) * (s.l2 u ^ 2 + s.energy u) <=
        1 / (s.poincareConstant ^ 2 + 1) *
          (s.energy u * (s.poincareConstant ^ 2 + 1)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    _ = s.energy u := by field_simp


/-- The anisotropic base case, conditional on uniform ellipticity of the symmetric part. -/
theorem anisotropic_coercive (D : Matrix (Fin dim) (Fin dim) Real) (alpha : Real)
    (halpha : 0 < alpha) (hD : Space.UniformElliptic D alpha)
    (u : FunctionSpace dim) (hu : s.admissible u) :
    (alpha * s.coercivityConstant) * s.h1 u ^ 2 <= s.anisotropic D u u := by
  have hd := s.diffusion_coercive u hu
  rw [s.toSpace.diffusion_self u hu] at hd
  calc
    (alpha * s.coercivityConstant) * s.h1 u ^ 2 =
        alpha * (s.coercivityConstant * s.h1 u ^ 2) := by ring
    _ <= alpha * s.energy u := mul_le_mul_of_nonneg_left hd halpha.le
    _ <= s.anisotropic D u u := s.toSpace.anisotropic_energy D alpha hD u hu

/-- Paper lemma "Skew-symmetry of the Advection Proof-Carrying Integrator".
Zero-boundary integration by parts is supplied by the selected analytic space. -/
theorem advection_skew (beta : Fin dim -> Real) (u v : FunctionSpace dim)
    (hu : s.admissible u) (hv : s.admissible v) :
    s.advection beta u v = -s.advection beta v u := by
  unfold Space.advection
  simp_rw [s.integrationByParts u hu v hv, mul_neg]
  rw [Finset.sum_neg_distrib]

/-- Gradient is the coordinate-velocity instance of the same integration-by-parts identity. -/
theorem gradient_skew (k : Fin dim) (u v : FunctionSpace dim)
    (hu : s.admissible u) (hv : s.admissible v) :
    s.gradient k u v = -s.gradient k v u := s.integrationByParts u hu v hv k

/-- Paper theorem "Proof-carrying integrator coercivity": positive coercive terms,
nonnegative mass terms, and arbitrary skew terms preserve the stated lower bound. -/
theorem composition_coercive {nH nL nS : Nat}
    (H : Fin nH -> FunctionSpace dim -> FunctionSpace dim -> Real)
    (L : Fin nL -> FunctionSpace dim -> FunctionSpace dim -> Real)
    (S : Fin nS -> FunctionSpace dim -> FunctionSpace dim -> Real)
    (c k : Fin nH -> Real) (d : Fin nL -> Real) (e : Fin nS -> Real)
    (hc : forall i, 0 < c i) (hk : forall i, 0 < k i) (hd : forall i, 0 <= d i)
    (hne : Nonempty (Fin nH))
    (hH : forall i u, s.admissible u -> k i * s.h1 u ^ 2 <= H i u u)
    (hL : forall i u, s.admissible u -> 0 <= L i u u)
    (hS : forall i u v, s.admissible u -> s.admissible v -> S i u v = -S i v u) :
    0 < Finset.univ.sum (fun i => c i * k i) /\
      forall u, s.admissible u ->
        (Finset.univ.sum (fun i => c i * k i)) * s.h1 u ^ 2 <=
          Finset.univ.sum (fun i => c i * H i u u) +
          Finset.univ.sum (fun i => d i * L i u u) +
          Finset.univ.sum (fun i => e i * S i u u) := by
  constructor
  . exact Finset.sum_pos (fun i _ => mul_pos (hc i) (hk i)) Finset.univ_nonempty
  . intro u hu
    have hskew (i : Fin nS) : S i u u = 0 := by
      have h := hS i u u hu hu
      linarith
    simp_rw [hskew, mul_zero, Finset.sum_const_zero, add_zero]
    have hmass : 0 <= Finset.univ.sum (fun i => d i * L i u u) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (hL i u hu)
    have hcoercive : Finset.univ.sum (fun i => c i * k i) * s.h1 u ^ 2 <=
        Finset.univ.sum (fun i => c i * H i u u) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hH i u hu) (hc i).le
    linarith

end ZeroBoundarySpace
end Variational

/-- Composition constraints of Section 3.2, attached to the actual IR_FORM syntax.
A positive total lower bound requires at least one H1-coercive term. -/
inductive TopLevel.EnergyCertificate {dim : Nat} (s : Variational.ZeroBoundarySpace dim) :
    TopLevel dim -> Real -> Prop where
  | mass (c : Realish) (hc : 0 < c) :
      TopLevel.EnergyCertificate s (.Coeff c (.mul .test .trial)) 0
  | diffusion (c : Realish) (hc : 0 < c) :
      TopLevel.EnergyCertificate s (.Coeff c (.inner .gradTest .gradTrial))
        ((c : Real) * s.coercivityConstant)
  | anisotropic (c : Realish) (hc : 0 < c) (D : DiffusionTensor dim)
      (alpha : Real) (halpha : 0 < alpha)
      (hD : Variational.Space.UniformElliptic (D.map (algebraMap Realish Real)) alpha) :
      TopLevel.EnergyCertificate s (.Coeff c (.inner .gradTest (.matMul D .gradTrial)))
        ((c : Real) * (alpha * s.coercivityConstant))
  | advection (c : Realish) (beta : VelocityVector dim) :
      TopLevel.EnergyCertificate s (.Coeff c (.mul .test (.inner (.velVec beta) .gradTrial))) 0
  | gradient (c : Realish) (k : Fin dim) :
      TopLevel.EnergyCertificate s (.Coeff c (.mul .test (.pDeriv .gradTrial k))) 0
  | integral {e : ScalarExpr dim} {r : Real}
      (h : TopLevel.EnergyCertificate s (.Coeff 1 e) r) :
      TopLevel.EnergyCertificate s (.Integral e) r
  | commute_mul {a b : ScalarExpr dim} {c : Realish} {r : Real}
      (h : TopLevel.EnergyCertificate s (.Coeff c (.mul a b)) r) :
      TopLevel.EnergyCertificate s (.Coeff c (.mul b a)) r
  | sum {a b : TopLevel dim} {A B : Real}
      (ha : TopLevel.EnergyCertificate s a A) (hb : TopLevel.EnergyCertificate s b B) :
      TopLevel.EnergyCertificate s (.Sum a b) (A + B)

/-- Valid left-hand sides carry a strictly positive certified lower bound. -/
def TopLevel.Valid {dim : Nat} (f : TopLevel dim)
                   (s :Variational.ZeroBoundarySpace dim) : Prop :=
    exists r : Real, 0 < r /\ f.EnergyCertificate s r /\ f.checkCoeffs

/-- Paper theorem "Proof-carrying integrator coercivity", for the actual syntax
and its integral semantics, conditional on the explicit zero-boundary interface. -/
theorem TopLevel.energy_of_certificate {dim : Nat} {s : Variational.ZeroBoundarySpace dim}
    {f : TopLevel dim} {r : Real} (h : f.EnergyCertificate s r)
    (u : Variational.FunctionSpace dim) (hu : s.admissible u) :
    r * s.h1 u ^ 2 <= f.analytic s.toSpace u u := by
  induction h with
  | mass c hc =>
      simpa [TopLevel.analytic, ScalarExpr.atFunctions] using
        mul_nonneg (show (0 : Real) <= c by exact_mod_cast hc.le) (s.toSpace.mass_self_nonneg u)
  | diffusion c hc =>
      simpa [TopLevel.analytic, s.toSpace.analytic_diffusion u u hu hu, mul_assoc] using
        mul_le_mul_of_nonneg_left (s.diffusion_coercive u hu)
          (show (0 : Real) <= c by exact_mod_cast hc.le)
  | anisotropic c hc D alpha halpha hD =>
      simpa [TopLevel.analytic, s.toSpace.analytic_anisotropic D u u hu hu, mul_assoc] using
        mul_le_mul_of_nonneg_left (s.anisotropic_coercive _ alpha halpha hD u hu)
          (show (0 : Real) <= c by exact_mod_cast hc.le)
  | advection c beta =>
      have h := s.advection_skew (fun k => (beta k : Real)) u u hu hu
      have hz : s.advection (fun k => (beta k : Real)) u u = 0 := by linarith
      simp [TopLevel.analytic, s.toSpace.analytic_advection beta u u hu hu, hz]
  | gradient c k =>
      have h := s.gradient_skew k u u hu hu
      have hz : s.gradient k u u = 0 := by linarith
      change 0 * s.h1 u ^ 2 <= (c : Real) * s.gradient k u u
      simp [hz]
  | integral h ih => simpa [TopLevel.analytic] using ih
  | commute_mul h ih =>
      simpa only [TopLevel.analytic, ScalarExpr.atFunctions, mul_comm] using ih
  | sum ha hb ia ib =>
      simpa only [TopLevel.analytic, add_mul] using add_le_add ia ib

/-- Every valid top-level form is coercive on its specified zero-boundary space. -/
theorem TopLevel.coercive_of_valid {dim : Nat} {s : Variational.ZeroBoundarySpace dim}
    {f : TopLevel dim} (h : f.Valid s) :
    exists r : Real, 0 < r /\ forall u, s.admissible u ->
      r * s.h1 u ^ 2 <= f.analytic s.toSpace u u := by
  cases h with
  | intro r hr =>
      exact Exists.intro r (And.intro hr.1 (fun u hu => TopLevel.energy_of_certificate hr.2.1 u hu))

/-- The coercivity-to-nonsingularity step mentioned in Section 6.2.
The reconstruction identity and positivity of the reconstructed H1 norm must be
established by a conforming finite-element space with correctly identified boundary data. -/
theorem stiffness_nonsingular_of_energy {n : Nat} (K : Matrix (Fin n) (Fin n) Real)
    (normSq : (Fin n -> Real) -> Real) (c : Real) (hc : 0 < c)
    (hpos : forall x, Ne x 0 -> 0 < normSq x)
    (henergy : forall x, c * normSq x <=
      Finset.univ.sum (fun i => x i * (K.mulVec x) i)) : Ne K.det 0 := by
  intro hdet
  have hkernel := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  cases hkernel with
  | intro x hx =>
      have hp := mul_pos hc (hpos x hx.1)
      have he := henergy x
      rw [hx.2] at he
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at he
      linarith
