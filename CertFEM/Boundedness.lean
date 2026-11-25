/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.PCI
import CertFEM.DefPCI

/-! # PCI Boundedness -/

-- NOTE: no computation for this section, so use Real instead of Realish

def PCI.bounded {dim : PNat} (pci : PCI dim) : Prop :=
  exists C : Real, 0 < C /\
    forall
      (basis : Fin ((dim : Nat) + 1) ->
        MvPolynomial (Fin dim) Realish)
      (i j : Fin ((dim : Nat) + 1)),
      (forall k, (basis k).totalDegree <= 1) ->
      |pci.analyticIntegral basis i j| <=
        C * pci.norm (evalPoly (basis i)) *
            pci.norm (evalPoly (basis j))

def PCI.boundedLinear {dim : PNat} (pci : PCI dim) : Prop :=
  exists C : Real, 0 < C /\
    forall
      (basis : Fin ((dim : Nat) + 1) ->
        MvPolynomial (Fin dim) Realish)
      (i j : Fin ((dim : Nat) + 1)),
      (forall k, (basis k).totalDegree <= 1) ->
      |pci.analyticIntegral basis i j| <=
        C * pci.norm (evalPoly (basis i))

/-! ## Boundedness proofs -/

lemma integral_mul_le_l2Norm
    {X : Type*} [MeasurableSpace X]
    (mu : MeasureTheory.Measure X)
    (u v : X -> Real)
    (hu : MeasureTheory.MemLp u 2 mu)
    (hv : MeasureTheory.MemLp v 2 mu) :
    |MeasureTheory.integral mu (fun x => u x * v x)| <=
      MeasureTheory.lpNorm u 2 mu *
      MeasureTheory.lpNorm v 2 mu := by

  have huNorm :
      MeasureTheory.lpNorm u 2 mu =
        (MeasureTheory.integral mu
          (fun x => norm (u x) ^ (2 : Real))) ^ (1 / (2 : Real)) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (p := (2 : ENNReal))
      (by norm_num) (by norm_num) hu.aestronglyMeasurable]
    norm_num

  have hvNorm :
      MeasureTheory.lpNorm v 2 mu =
        (MeasureTheory.integral mu
          (fun x => norm (v x) ^ (2 : Real))) ^ (1 / (2 : Real)) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (p := (2 : ENNReal))
      (by norm_num) (by norm_num) hv.aestronglyMeasurable]
    norm_num

  have hu' : MeasureTheory.MemLp u (ENNReal.ofReal (2 : Real)) mu := by
    simpa only [ENNReal.ofReal_ofNat] using hu

  have hv' : MeasureTheory.MemLp v (ENNReal.ofReal (2 : Real)) mu := by
    simpa only [ENNReal.ofReal_ofNat] using hv

  have hHolder :=
    MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (p := (2 : Real)) (q := (2 : Real))
      Real.HolderConjugate.two_two hu' hv'

  calc
    |MeasureTheory.integral mu (fun x => u x * v x)|
        <= MeasureTheory.integral mu
          (fun x => norm (u x) * norm (v x)) := by
            simpa only [Real.norm_eq_abs, norm_mul] using
              (MeasureTheory.norm_integral_le_integral_norm
                (fun x : X => u x * v x))
    _ <= MeasureTheory.lpNorm u 2 mu *
        MeasureTheory.lpNorm v 2 mu := by
          rw [huNorm, hvNorm]
          exact hHolder

lemma evalPoly_memLp_of_isCompact
    {dim : Nat}
    (p : MvPolynomial (Fin dim) Realish)
    {s : Set (Fin dim -> Real)}
    (hs : IsCompact s) :
    MeasureTheory.MemLp (evalPoly p) 2
      (MeasureTheory.volume.restrict s) := by
  have hc : Continuous (evalPoly p) := by
    simpa only [evalPoly] using
      (MvPolynomial.continuous_eval
        (MvPolynomial.map (algebraMap Realish Real) p))

  have hb :
      BddAbove
        ((fun x : Fin dim -> Real => norm (evalPoly p x)) '' s) :=
    hs.bddAbove_image hc.norm.continuousOn

  cases hb with
  | intro C hC =>
    have hBound :
        forall x : Fin dim -> Real,
          Set.Mem s x -> norm (evalPoly p x) <= C := by
      intro x hx
      exact hC (Set.mem_image_of_mem _ hx)

    have : MeasureTheory.IsFiniteMeasure
        (MeasureTheory.volume.restrict s) :=
      (MeasureTheory.isFiniteMeasure_restrict).2 hs.measure_ne_top

    apply MeasureTheory.MemLp.of_bound
      hc.aestronglyMeasurable C

    filter_upwards [MeasureTheory.ae_restrict_mem
      hs.isClosed.measurableSet] with x hx
    exact hBound x hx

/-- Paper lemma "Boundedness of the Mass Integrator" (Section 6.1). -/
lemma massIntegratorBounded {dim : PNat} :
    (massPCI dim).bounded := by
  refine Exists.intro (1 : Real) ?_
  constructor
  case left =>
    norm_num
  case right =>
    intro basis i j hdegree

    have hDomain :
        (massPCI dim).realDomain =
          realDomainOfSimplex (refSimplexND dim) := by
      rfl

    have hCompact :
        IsCompact ((massPCI dim).realDomain) := by
      rw [hDomain]
      unfold realDomainOfSimplex
      exact (Set.finite_range _).isCompact_convexHull Real

    have hu := evalPoly_memLp_of_isCompact
      (basis i) hCompact

    have hv := evalPoly_memLp_of_isCompact
      (basis j) hCompact

    have h := integral_mul_le_l2Norm
      (MeasureTheory.volume.restrict
        (massPCI dim).realDomain)
      (evalPoly (basis i))
      (evalPoly (basis j))
      hu hv

    simpa [PCI.analyticIntegral, PCI.norm, PCI.l2Norm,
      massPCI, hDomain, evalPoly,
      map_mul, MvPolynomial.eval_mul] using h

/-! ## Analytic forms on a specified function space

The space supplies square-integrability, rather than silently treating every function as H1.
Zero-boundary hypotheses are added separately in Coercivity.lean.
-/

namespace Variational

abbrev FunctionSpace (dim : Nat) := (Fin dim -> Real) -> Real

structure Space (dim : Nat) where
  measure : MeasureTheory.Measure (Fin dim -> Real)
  admissible : Set (FunctionSpace dim)
  memLp : forall u, admissible u -> MeasureTheory.MemLp u 2 measure
  derivMemLp : forall u, admissible u -> forall k,
    MeasureTheory.MemLp (partialDeriv k u) 2 measure

namespace Space

variable {dim : Nat} (s : Space dim)

noncomputable def l2 (u : FunctionSpace dim) : Real := MeasureTheory.lpNorm u 2 s.measure

noncomputable def energy (u : FunctionSpace dim) : Real :=
  Finset.univ.sum fun k => (MeasureTheory.lpNorm (partialDeriv k u) 2 s.measure) ^ 2

noncomputable def h1 (u : FunctionSpace dim) : Real := Real.sqrt (s.l2 u ^ 2 + s.energy u)

noncomputable def mass (u v : FunctionSpace dim) : Real :=
  MeasureTheory.integral s.measure (fun x => u x * v x)

noncomputable def gradient (k : Fin dim) (u v : FunctionSpace dim) : Real :=
  MeasureTheory.integral s.measure (fun x => u x * partialDeriv k v x)

noncomputable def diffusion (u v : FunctionSpace dim) : Real :=
  Finset.univ.sum fun k =>
    MeasureTheory.integral s.measure (fun x => partialDeriv k u x * partialDeriv k v x)

noncomputable def advection (beta : Fin dim -> Real) (u v : FunctionSpace dim) : Real :=
  Finset.univ.sum fun k => beta k * s.gradient k u v

noncomputable def anisotropic (D : Matrix (Fin dim) (Fin dim) Real)
    (u v : FunctionSpace dim) : Real :=
  Finset.univ.sum fun k => Finset.univ.sum fun l => D k l *
    MeasureTheory.integral s.measure (fun x => partialDeriv k u x * partialDeriv l v x)

/-- Paper definition "Lax--Milgram boundedness", with an explicit bound. -/
def Bound (a : FunctionSpace dim -> FunctionSpace dim -> Real) (C : Real) : Prop :=
  forall u, s.admissible u -> forall v, s.admissible v ->
    |a u v| <= C * s.h1 u * s.h1 v

lemma energy_nonneg (u : FunctionSpace dim) : 0 <= s.energy u := by
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

lemma h1_nonneg (u : FunctionSpace dim) : 0 <= s.h1 u := Real.sqrt_nonneg _

lemma h1_sq (u : FunctionSpace dim) : s.h1 u ^ 2 = s.l2 u ^ 2 + s.energy u := by
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (s.energy_nonneg u))

lemma l2_le_h1 (u : FunctionSpace dim) : s.l2 u <= s.h1 u := by
  apply Real.le_sqrt_of_sq_le
  linarith [s.energy_nonneg u]

lemma deriv_le_h1 (u : FunctionSpace dim) (k : Fin dim) :
    MeasureTheory.lpNorm (partialDeriv k u) 2 s.measure <= s.h1 u := by
  apply Real.le_sqrt_of_sq_le
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun l => MeasureTheory.lpNorm (partialDeriv l u) 2 s.measure ^ 2)
    (fun l _ => sq_nonneg _) (Finset.mem_univ k)
  dsimp [energy] at *
  nlinarith [sq_nonneg (s.l2 u)]

/-- Paper lemma "Boundedness of the Mass Integrator": the H1 bound has constant one. -/
theorem mass_bound : s.Bound s.mass 1 := by
  intro u hu v hv
  have h := integral_mul_le_l2Norm s.measure u v (s.memLp u hu) (s.memLp v hv)
  calc
    |s.mass u v| <= s.l2 u * s.l2 v := h
    _ <= s.h1 u * s.h1 v :=
      mul_le_mul (s.l2_le_h1 u) (s.l2_le_h1 v)
        MeasureTheory.lpNorm_nonneg (s.h1_nonneg u)
    _ = 1 * s.h1 u * s.h1 v := by ring

/-- Boundedness of the Gradient integrator in the common H1 norm. -/
theorem gradient_bound (k : Fin dim) : s.Bound (s.gradient k) 1 := by
  intro u hu v hv
  have h := integral_mul_le_l2Norm s.measure u (partialDeriv k v)
    (s.memLp u hu) (s.derivMemLp v hv k)
  calc
    |s.gradient k u v| <= s.l2 u *
        MeasureTheory.lpNorm (partialDeriv k v) 2 s.measure := h
    _ <= s.h1 u * s.h1 v :=
      mul_le_mul (s.l2_le_h1 u) (s.deriv_le_h1 v k)
        MeasureTheory.lpNorm_nonneg (s.h1_nonneg u)
    _ = 1 * s.h1 u * s.h1 v := by ring

lemma bound_scale {a : FunctionSpace dim -> FunctionSpace dim -> Real} {C : Real}
    (ha : s.Bound a C) (c : Real) : s.Bound (fun u v => c * a u v) (|c| * C) := by
  intro u hu v hv
  calc
    |c * a u v| = |c| * |a u v| := abs_mul _ _
    _ <= |c| * (C * s.h1 u * s.h1 v) :=
      mul_le_mul_of_nonneg_left (ha u hu v hv) (abs_nonneg _)
    _ = _ := by ring

/-- Paper theorem "Proof-carrying integrator boundedness": finite composition
has the sum of the absolute coefficient times primitive bound as its bound. -/
theorem bound_sum {n : Nat} (a : Fin n -> FunctionSpace dim -> FunctionSpace dim -> Real)
    (C c : Fin n -> Real) (ha : forall k, s.Bound (a k) (C k)) :
    s.Bound (fun u v => Finset.univ.sum fun k => c k * a k u v)
      (Finset.univ.sum fun k => |c k| * C k) := by
  intro u hu v hv
  calc
    |Finset.univ.sum (fun k => c k * a k u v)| <=
        Finset.univ.sum (fun k => |c k * a k u v|) := Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.univ.sum (fun k => (|c k| * C k) * s.h1 u * s.h1 v) :=
      Finset.sum_le_sum fun k _ => s.bound_scale (ha k) (c k) u hu v hv
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

/-- Diffusion is bounded; this dimension-dependent bound avoids a separate vector Holder lemma. -/
theorem diffusion_bound : s.Bound s.diffusion dim := by
  intro u hu v hv
  calc
    |s.diffusion u v| <= Finset.univ.sum (fun k =>
        |MeasureTheory.integral s.measure
          (fun x => partialDeriv k u x * partialDeriv k v x)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.univ.sum (fun _ : Fin dim => s.h1 u * s.h1 v) := by
      apply Finset.sum_le_sum
      intro k _
      exact (integral_mul_le_l2Norm s.measure _ _
        (s.derivMemLp u hu k) (s.derivMemLp v hv k)).trans
        (mul_le_mul (s.deriv_le_h1 u k) (s.deriv_le_h1 v k)
          MeasureTheory.lpNorm_nonneg (s.h1_nonneg u))
    _ = (dim : Real) * s.h1 u * s.h1 v := by simp [mul_assoc]

/-- Advection is bounded by the sum of the absolute velocity components. -/
theorem advection_bound (beta : Fin dim -> Real) :
    s.Bound (s.advection beta) (Finset.univ.sum fun k => |beta k|) := by
  simpa only [mul_one] using
    s.bound_sum (fun k => s.gradient k) (fun _ => 1) beta s.gradient_bound

/-- Anisotropic diffusion is bounded for every constant tensor, without a positivity assumption. -/
theorem anisotropic_bound (D : Matrix (Fin dim) (Fin dim) Real) :
    s.Bound (s.anisotropic D) (Finset.univ.sum fun k => Finset.univ.sum fun l => |D k l|) := by
  intro u hu v hv
  calc
    |s.anisotropic D u v| <= Finset.univ.sum (fun k =>
        Finset.univ.sum fun l => |D k l * MeasureTheory.integral s.measure
          (fun x => partialDeriv k u x * partialDeriv l v x)|) :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _)
    _ <= Finset.univ.sum (fun k => Finset.univ.sum fun l =>
        |D k l| * (s.h1 u * s.h1 v)) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (integral_mul_le_l2Norm s.measure _ _
        (s.derivMemLp u hu k) (s.derivMemLp v hv l)).trans
        (mul_le_mul (s.deriv_le_h1 u k) (s.deriv_le_h1 v l)
          MeasureTheory.lpNorm_nonneg (s.h1_nonneg u))
    _ = _ := by simp_rw [<- Finset.sum_mul]; ring

/-- The Linear integrator is a bounded functional whenever its source is square-integrable. -/
theorem linear_bound (f : FunctionSpace dim) (hf : MeasureTheory.MemLp f 2 s.measure)
    (u : FunctionSpace dim) (hu : s.admissible u) :
    |MeasureTheory.integral s.measure (fun x => f x * u x)| <=
      MeasureTheory.lpNorm f 2 s.measure * s.h1 u := by
  exact (integral_mul_le_l2Norm s.measure f u hf (s.memLp u hu)).trans
    (mul_le_mul_of_nonneg_left (s.l2_le_h1 u) MeasureTheory.lpNorm_nonneg)

end Space
end Variational

/-- Pointwise vector semantics on actual functions, for the analytic layer. -/
noncomputable def VectorExpr.atFunctions {dim : Nat} (e : VectorExpr dim)
    (u v : Variational.FunctionSpace dim) (x : Fin dim -> Real) : Fin dim -> Real :=
  match e with
  | .gradTest => fun k => partialDeriv k u x
  | .gradTrial => fun k => partialDeriv k v x
  | .velVec beta => fun k => (beta k : Real)
  | .matMul D a => fun k => Finset.univ.sum fun l =>
      (D k l : Real) * a.atFunctions u v x l

/-- Pointwise scalar semantics on actual functions. -/
noncomputable def ScalarExpr.atFunctions {dim : Nat} (e : ScalarExpr dim)
    (u v : Variational.FunctionSpace dim) (x : Fin dim -> Real) : Real :=
  match e with
  | .test => u x
  | .trial => v x
  | .sReal c => c
  | .mul a b => a.atFunctions u v x * b.atFunctions u v x
  | .inner a b => Finset.univ.sum fun k =>
      a.atFunctions u v x k * b.atFunctions u v x k
  | .pDeriv a k => a.atFunctions u v x k

/-- Integral semantics of the actual top-level syntax on the selected analytic space. -/
noncomputable def TopLevel.analytic {dim : Nat} (f : TopLevel dim)
    (s : Variational.Space dim) (u v : Variational.FunctionSpace dim) : Real :=
  match f with
  | .Integral e => MeasureTheory.integral s.measure (e.atFunctions u v)
  | .Coeff c e => (c : Real) * MeasureTheory.integral s.measure (e.atFunctions u v)
  | .Sum a b => a.analytic s u v + b.analytic s u v

/-- Bounds propagate through every supported top-level constructor. -/
inductive TopLevel.BoundCertificate {dim : Nat} (s : Variational.Space dim) :
    TopLevel dim -> Real -> Prop where
  | integral (e : ScalarExpr dim) (C : Real)
      (h : s.Bound (fun u v => MeasureTheory.integral s.measure (e.atFunctions u v)) C) :
      TopLevel.BoundCertificate s (.Integral e) C
  | coeff (e : ScalarExpr dim) (C : Real) (c : Realish)
      (h : s.Bound (fun u v => MeasureTheory.integral s.measure (e.atFunctions u v)) C) :
      TopLevel.BoundCertificate s (.Coeff c e) (|(c : Real)| * C)
  | sum {a b : TopLevel dim} {A B : Real}
      (ha : TopLevel.BoundCertificate s a A) (hb : TopLevel.BoundCertificate s b B) :
      TopLevel.BoundCertificate s (.Sum a b) (A + B)

/-- Paper theorem "Proof-carrying integrator boundedness", on the actual form syntax. -/
theorem TopLevel.bounded_of_certificate {dim : Nat} {s : Variational.Space dim}
    {f : TopLevel dim} {C : Real} (h : f.BoundCertificate s C) :
    s.Bound (f.analytic s) C := by
  induction h with
  | integral e C h => exact h
  | coeff e C c h => exact s.bound_scale h c
  | sum ha hb ia ib =>
      intro u hu v hv
      exact (abs_add_le _ _).trans (by
        nlinarith [ia u hu v hv, ib u hu v hv])

namespace Variational.Space

variable {dim : Nat} (s : Space dim)

lemma analytic_diffusion (u v : FunctionSpace dim) (hu : s.admissible u)
    (hv : s.admissible v) :
    MeasureTheory.integral s.measure
      ((ScalarExpr.inner .gradTest .gradTrial).atFunctions u v) = s.diffusion u v := by
  exact MeasureTheory.integral_finsetSum _ fun k _ =>
    (s.derivMemLp u hu k).integrable_mul (s.derivMemLp v hv k)

lemma analytic_advection (beta : VelocityVector dim) (u v : FunctionSpace dim)
    (hu : s.admissible u) (hv : s.admissible v) :
    MeasureTheory.integral s.measure
      ((ScalarExpr.mul .test (.inner (.velVec beta) .gradTrial)).atFunctions u v) =
      s.advection (fun k => (beta k : Real)) u v := by
  simp only [ScalarExpr.atFunctions, VectorExpr.atFunctions, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum]
  . apply Finset.sum_congr rfl
    intro k _
    simp_rw [mul_left_comm (u _) (beta k : Real)]
    exact MeasureTheory.integral_const_mul _ _
  . intro k _
    simpa only [Pi.mul_apply, mul_left_comm] using
      ((s.memLp u hu).integrable_mul (s.derivMemLp v hv k)).const_mul (beta k : Real)

lemma analytic_anisotropic (D : DiffusionTensor dim) (u v : FunctionSpace dim)
    (hu : s.admissible u) (hv : s.admissible v) :
    MeasureTheory.integral s.measure
      ((ScalarExpr.inner .gradTest (.matMul D .gradTrial)).atFunctions u v) =
      s.anisotropic (D.map (algebraMap Realish Real)) u v := by
  simp only [ScalarExpr.atFunctions, VectorExpr.atFunctions, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum]
  . apply Finset.sum_congr rfl
    intro k _
    rw [MeasureTheory.integral_finsetSum]
    . apply Finset.sum_congr rfl
      intro l _
      simp_rw [mul_left_comm (partialDeriv k u _) (D k l : Real)]
      exact MeasureTheory.integral_const_mul _ _
    . intro l _
      simpa only [Pi.mul_apply, mul_left_comm] using
        ((s.derivMemLp u hu k).integrable_mul (s.derivMemLp v hv l)).const_mul (D k l : Real)
  . intro k _
    apply MeasureTheory.integrable_finsetSum
    intro l _
    simpa only [Pi.mul_apply, mul_left_comm] using
      ((s.derivMemLp u hu k).integrable_mul (s.derivMemLp v hv l)).const_mul (D k l : Real)

end Variational.Space

/-- The canonical primitive bounds apply to the integral semantics used by IR_FORM. -/
theorem massAnalyticBound {dim : Nat} (s : Variational.Space dim) :
    s.Bound (fun u v => MeasureTheory.integral s.measure
      ((ScalarExpr.mul .test .trial).atFunctions u v)) 1 := s.mass_bound

/-- Diffusion's integral syntax has the same bound as its analytic form. -/
theorem diffusionAnalyticBound {dim : Nat} (s : Variational.Space dim) :
    s.Bound (fun u v => MeasureTheory.integral s.measure
      ((ScalarExpr.inner .gradTest .gradTrial).atFunctions u v)) dim := by
  intro u hu v hv
  dsimp only
  rw [s.analytic_diffusion u v hu hv]
  exact s.diffusion_bound u hu v hv

/-- Advection's bound retains its velocity components. -/
theorem advectionAnalyticBound {dim : Nat} (s : Variational.Space dim) (beta : VelocityVector dim) :
    s.Bound (fun u v => MeasureTheory.integral s.measure
      ((ScalarExpr.mul .test (.inner (.velVec beta) .gradTrial)).atFunctions u v))
      (Finset.univ.sum fun k => |(beta k : Real)|) := by
  intro u hu v hv
  dsimp only
  rw [s.analytic_advection beta u v hu hv]
  exact s.advection_bound (fun k => (beta k : Real)) u hu v hv

/-- Anisotropic diffusion's bound retains every entry of its tensor. -/
theorem anisotropicAnalyticBound {dim : Nat} (s : Variational.Space dim) (D : DiffusionTensor dim) :
    s.Bound (fun u v => MeasureTheory.integral s.measure
      ((ScalarExpr.inner .gradTest (.matMul D .gradTrial)).atFunctions u v))
      (Finset.univ.sum fun k => Finset.univ.sum fun l => |(D k l : Real)|) := by
  intro u hu v hv
  dsimp only
  rw [s.analytic_anisotropic D u v hu hv]
  exact s.anisotropic_bound _ u hu v hv

/-- A bound certificate gives the strictly positive constant required by the paper,
including the empty or identically zero form cases where the sharp constant may be zero. -/
theorem TopLevel.bounded {dim : Nat} {s : Variational.Space dim} {f : TopLevel dim}
    {C : Real} (h : f.BoundCertificate s C) :
    exists B : Real, 0 < B /\ s.Bound (f.analytic s) B := by
  refine Exists.intro (|C| + 1) (And.intro (by positivity) ?_)
  intro u hu v hv
  apply (TopLevel.bounded_of_certificate h u hu v hv).trans
  apply mul_le_mul_of_nonneg_right _ (s.h1_nonneg v)
  apply mul_le_mul_of_nonneg_right _ (s.h1_nonneg u)
  linarith [le_abs_self C]
