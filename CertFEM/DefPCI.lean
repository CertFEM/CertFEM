/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.PCI

/- # Default set of PCIs -/

noncomputable def massPCI (dim : Nat) : PCI dim where
  grammar := .mul .test .trial
  kind := .l2Coercive
  checkCoefficient := fun c => 0 < c
  accumulator := fun q basis detJ i j =>
    quadSum q detJ (fun g =>
      basisAt q basis g i * basisAt q basis g j)
  integrand := fun u v => u * v

noncomputable def diffusionPCI (dim : Nat) : PCI dim where
  grammar := .inner .gradTest .gradTrial
  kind := .h1Coercive
  checkCoefficient := fun c => 0 < c
  accumulator := fun q basis detJ i j =>
    quadSum q detJ (fun g =>
      dotProduct (gradAt q basis g i) (gradAt q basis g j))
  integrand := fun u v =>
    Finset.univ.sum (fun k : Fin dim =>
      MvPolynomial.pderiv k u *
      MvPolynomial.pderiv k v)

noncomputable def gradientPCI (dim : PNat) (dir : Fin dim) : PCI dim where
  grammar := .mul .test (.pDeriv .gradTrial dir)
  kind := .h1Skew
  accumulator := fun q basis detJ i j =>
    quadSum q detJ (fun g =>
      basisAt q basis g i * gradAt q basis g j dir)
  integrand := fun u v =>
    u * MvPolynomial.pderiv dir v

noncomputable def anisotropicDiffusionPCI (dim : Nat)
                  (D : DiffusionTensor dim) : PCI dim where
  grammar := .inner .gradTest (.matMul D .gradTrial)
  kind := .h1Coercive
  checkCoefficient := fun c => 0 < c
  accumulator := fun q basis detJ i j =>
  quadSum q detJ (fun g =>
    dotProduct (gradAt q basis g i)
               ((D.map (algebraMap Realish Real)).mulVec (gradAt q basis g j)))
  integrand := fun u v =>
    Finset.univ.sum (fun k : Fin dim =>
      MvPolynomial.pderiv k u *
        Finset.univ.sum (fun l : Fin dim =>
          MvPolynomial.C (D k l) *
            MvPolynomial.pderiv l v))

noncomputable def advectionPCI (dim : Nat) (beta : (Fin dim) -> Realish) : PCI dim where
  grammar := .mul .test (.inner (.velVec beta) .gradTrial)
  kind := .h1Skew
  accumulator := fun q basis detJ i j =>
    quadSum q detJ (fun g =>
      basisAt q basis g i *
        dotProduct (fun d => (beta d : Real)) (gradAt q basis g j))
  integrand := fun u v =>
    u * Finset.univ.sum (fun k : Fin dim =>
      MvPolynomial.C (beta k) *
        MvPolynomial.pderiv k v)

noncomputable def linearPCI (dim : Nat) (f : Realish) : PCI dim where
  grammar := .mul (.sReal f) .test
  kind := .linear
  accumulator := fun q basis detJ i =>
    quadSum q detJ (fun g =>
      f * basisAt q basis g i)
  integrand := fun u _ =>
    MvPolynomial.C f * u

/-! ## PCI helpers -/

inductive PCITag where
  | mass
  | diffusion
  | anisotropicDiffusion
  | advection
  | gradient
  | linear
  deriving DecidableEq, Repr

def matchPCI {dim : Nat} (e : ScalarExpr dim) : Option PCITag :=
  match e with
  | .mul .test .trial | .mul .trial .test =>
      some .mass
  | .inner .gradTest .gradTrial | .inner .gradTrial .gradTest =>
      some .diffusion
  | .inner .gradTest (.matMul _ .gradTrial) =>
      some .anisotropicDiffusion
  | .mul .test (.inner (.velVec _) .gradTrial)
  | .mul (.inner (.velVec _) .gradTrial) .test =>
      some .advection
  | .mul .test (.pDeriv .gradTrial _)
  | .mul (.pDeriv .gradTrial _) .test =>
      some .gradient
  | .mul (.sReal _) .test | .mul .test (.sReal _) =>
      some .linear
  | _ =>
      none

noncomputable def pciSpecification {dim : PNat}
    (tag : PCITag) : PCI dim :=
  match tag with
  | .mass => massPCI dim
  | .diffusion => diffusionPCI dim
  | .anisotropicDiffusion =>
      anisotropicDiffusionPCI dim (Matrix.diagonal (fun _ => 1))
  | .advection =>
      advectionPCI dim (fun _ => 1)
  | .gradient => gradientPCI dim 0
  | .linear => linearPCI dim 1

def TopLevel.checkCoeffs {dim : Nat} : TopLevel dim -> Prop
  | .Integral e =>
      if h : 0 < dim then
        match matchPCI e with
        | some tag =>
            (pciSpecification
              (dim := Subtype.mk dim h) tag).checkCoefficient 1
        | none => False
      else False
  | .Coeff r e =>
      if h : 0 < dim then
        match matchPCI e with
        | some tag =>
            (pciSpecification
              (dim := Subtype.mk dim h) tag).checkCoefficient r
        | none => False
      else False
  | .Sum e1 e2 =>
      e1.checkCoeffs /\ e2.checkCoeffs

/-! ## Proofs for default PCIs -/

lemma massFormOk : forall dim : Nat, formEqIntegrand (massPCI dim) := by
  intro dim basis i j
  rfl

lemma massAccOk :
    forall dim : Nat, accEqIntegral (massPCI dim) := by
  intro dim basis i j nq maxDegree q hExact hDegree

  have hq := hExact (basis i * basis j) hDegree

  change exactPolyIntegral (basis i * basis j) =
    quadSum q 1
      (fun g => basisAt q basis g i * basisAt q basis g j)

  simpa [evalPoly, basisAt, map_mul, MvPolynomial.eval_mul]
    using hq.symm

lemma diffusionFormOk : forall dim : PNat, formEqIntegrand (diffusionPCI dim) := by
  intro dim basis i j
  rfl

lemma diffusionAccOk :
    forall (dim : Nat),
      accEqIntegral (diffusionPCI dim) := by
  intro dim
  apply accEqIntegral_of_eval
  intro basis i j nq q
  simp [diffusionPCI, AccumulatorOutput.get,
    evalPoly, gradAt, dotProduct,
    MvPolynomial.pderiv_map,
    map_sum, map_mul,
    MvPolynomial.eval_sum, MvPolynomial.eval_mul]

lemma gradientFormOk :
    forall (dim : PNat) (dir : Fin dim),
      formEqIntegrand (gradientPCI dim dir) := by
  intro dim dir basis i j
  rfl

lemma gradientAccOk :
    forall (dim : PNat) (dir : Fin dim),
      accEqIntegral (gradientPCI dim dir) := by
  intro dim dir
  apply accEqIntegral_of_eval
  intro basis i j nq q
  simp [gradientPCI, AccumulatorOutput.get,
    evalPoly, basisAt, gradAt,
    MvPolynomial.pderiv_map,
    map_mul, MvPolynomial.eval_mul]

lemma anisotropicDiffusionFormOk :
    forall (dim : Nat) (D : DiffusionTensor dim),
      formEqIntegrand (anisotropicDiffusionPCI dim D) := by
  intro dim D basis i j
  rfl

lemma anisotropicDiffusionAccOk :
    forall (dim : Nat) (D : DiffusionTensor dim),
      accEqIntegral (anisotropicDiffusionPCI dim D) := by
  intro dim D
  apply accEqIntegral_of_eval
  intro basis i j nq q
  simp [anisotropicDiffusionPCI, AccumulatorOutput.get,
    evalPoly, gradAt, dotProduct, Matrix.mulVec,
    Matrix.map_apply, MvPolynomial.pderiv_map]

lemma advectionFormOk :
    forall (dim : PNat) (beta : VelocityVector dim),
      formEqIntegrand (advectionPCI dim beta) := by
  intro dim beta basis i j
  rfl

lemma advectionAccOk :
    forall (dim : Nat) (f : VelocityVector dim),
      accEqIntegral (advectionPCI dim f) := by
  intro dim f
  apply accEqIntegral_of_eval
  intro basis i j nq q
  simp only [advectionPCI, AccumulatorOutput.get]
  apply congrArg (quadSum q 1)
  funext g
  simp [evalPoly, basisAt, gradAt, dotProduct,
    MvPolynomial.pderiv_map]

lemma linearFormOk :
    forall (dim : Nat) (f : Realish),
      formEqIntegrand (linearPCI dim f) := by
  intro dim f basis i j
  rfl

lemma linearAccOk :
    forall (dim : Nat) (f : Realish),
      accEqIntegral (linearPCI dim f) := by
  intro dim f
  apply accEqIntegral_of_eval
  intro basis i j nq q
  simp [linearPCI, AccumulatorOutput.get,
    evalPoly, basisAt, map_mul, MvPolynomial.eval_mul]

/-- Paper theorem "Mass Integrator Quadrature Exactness": any P1 mass product
is exact under a quadrature rule exact through degree two. -/
theorem massP1Exact {dim nq : Nat} (basis : P1Basis dim)
    (hbasis : forall i, (basis i).totalDegree <= 1) (q : QuadScheme dim nq)
    (hq : QuadExact q 2) (i j : Fin (dim + 1)) :
    (massPCI dim).integral (basis i) (basis j) =
      (massPCI dim).accumulator q basis 1 i j := by
  apply massAccOk dim basis i j nq 2 q hq
  exact (MvPolynomial.totalDegree_mul _ _).trans (by linarith [hbasis i, hbasis j])

/-- The (bi-)linearity obligation described in Section 3.1, over polynomial inputs. -/
structure PCI.Bilinear {dim : Nat} (pci : PCI dim) : Prop where
  add_left : forall u v w, pci.integrand (u + v) w = pci.integrand u w + pci.integrand v w
  add_right : forall u v w, pci.integrand u (v + w) = pci.integrand u v + pci.integrand u w
  scalar_left : forall c u v,
    pci.integrand (MvPolynomial.C c * u) v = MvPolynomial.C c * pci.integrand u v
  scalar_right : forall c u v,
    pci.integrand u (MvPolynomial.C c * v) = MvPolynomial.C c * pci.integrand u v

/-- Paper "(Bi-)linearity proof", Mass integrator. -/
theorem massBilinear (dim : Nat) : (massPCI dim).Bilinear := by
  constructor <;> intros <;> simp [massPCI] <;> ring

/-- Paper "(Bi-)linearity proof", Diffusion integrator. -/
theorem diffusionBilinear (dim : Nat) : (diffusionPCI dim).Bilinear := by
  constructor <;> intros <;>
    simp [diffusionPCI, mul_add, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Paper "(Bi-)linearity proof", Gradient integrator. -/
theorem gradientBilinear (dim : PNat) (k : Fin dim) : (gradientPCI dim k).Bilinear := by
  constructor <;> intros <;> simp [gradientPCI] <;> ring

/-- Paper "(Bi-)linearity proof", Advection integrator. -/
theorem advectionBilinear (dim : Nat) (beta : VelocityVector dim) :
    (advectionPCI dim beta).Bilinear := by
  constructor <;> intros <;>
    simp [advectionPCI, mul_add, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Paper "(Bi-)linearity proof", Anisotropic Diffusion integrator. -/
theorem anisotropicDiffusionBilinear (dim : Nat) (D : DiffusionTensor dim) :
    (anisotropicDiffusionPCI dim D).Bilinear := by
  constructor <;> intros <;>
    simp [anisotropicDiffusionPCI, mul_add, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Paper "(Bi-)linearity proof": the load integrator is linear in its test input. -/
theorem linearIntegratorLinear (dim : Nat) (f : Realish)
    (u v w : MvPolynomial (Fin dim) Realish) (c : Realish) :
    (linearPCI dim f).integrand (u + v) w =
      (linearPCI dim f).integrand u w + (linearPCI dim f).integrand v w /\
    (linearPCI dim f).integrand (MvPolynomial.C c * u) w =
      MvPolynomial.C c * (linearPCI dim f).integrand u w := by
  constructor <;> simp [linearPCI] <;> ring
