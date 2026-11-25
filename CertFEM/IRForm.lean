/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import Mathlib
import CertFEM.Simplex

/-! # IR_FORM -/

abbrev DiffusionTensor (dim : Nat) := Matrix (Fin dim) (Fin dim) Realish
abbrev VelocityVector (dim : Nat) := Fin dim -> Realish

inductive VectorExpr (dim : Nat) : Type where
  | gradTest  : VectorExpr dim
  | gradTrial : VectorExpr dim
  | velVec : VelocityVector dim -> VectorExpr dim
  | matMul : DiffusionTensor dim -> VectorExpr dim -> VectorExpr dim

inductive ScalarExpr (dim : Nat) : Type where
  | test  : ScalarExpr dim
  | trial : ScalarExpr dim
  | sReal : Realish -> ScalarExpr dim
  | mul   : ScalarExpr dim -> ScalarExpr dim -> ScalarExpr dim
  | inner : VectorExpr dim -> VectorExpr dim -> ScalarExpr dim
  | pDeriv : VectorExpr dim -> Fin dim -> ScalarExpr dim

inductive TopLevel (dim : Nat) : Type where
  | Integral : ScalarExpr dim -> TopLevel dim
  | Coeff    : Realish -> ScalarExpr dim -> TopLevel dim
  | Sum      : TopLevel dim -> TopLevel dim -> TopLevel dim

noncomputable def VectorExpr.denote {dim : Nat}
    (e : VectorExpr dim)
    (basis : Fin (dim + 1) -> MvPolynomial (Fin dim) Realish)
    : Fin (dim + 1) -> Fin (dim + 1) -> Fin dim -> MvPolynomial (Fin dim) Realish :=
  match e with
  | .gradTest =>
      fun i _ k => MvPolynomial.pderiv k (basis i)
  | .gradTrial =>
      fun _ j k => MvPolynomial.pderiv k (basis j)
  | .velVec beta =>
      fun _ _ k => MvPolynomial.C (beta k)
  | .matMul d v =>
      fun i j k =>
        Finset.univ.sum (fun l : Fin dim =>
          MvPolynomial.C (d k l) * (v.denote basis) i j l)

noncomputable def ScalarExpr.denote {dim : Nat}
    (e : ScalarExpr dim)
    (basis : Fin (dim + 1) -> MvPolynomial (Fin dim) Realish)
    : Fin (dim + 1) -> Fin (dim + 1) -> MvPolynomial (Fin dim) Realish :=
  match e with
  | test => fun i _ => basis i
  | trial => fun _ j => basis j
  | sReal r => fun _ _ => MvPolynomial.C r
  | mul e1 e2 => fun i j => (e1.denote basis i j) * (e2.denote basis i j)
  | .inner v1 v2 =>
      fun i j =>
        Finset.univ.sum (fun k : Fin dim =>
          v1.denote basis i j k * v2.denote basis i j k)
  | pDeriv e dir => fun i j => (e.denote basis) i j dir

def VectorExpr.sameShape {dim : Nat} : VectorExpr dim -> VectorExpr dim -> Bool
  | .gradTest, .gradTest => true
  | .gradTrial, .gradTrial => true
  | .velVec _, .velVec _ => true
  | .matMul _ a, .matMul _ b => sameShape a b
  | _, _ => false

def ScalarExpr.sameShape {dim : Nat} : ScalarExpr dim -> ScalarExpr dim -> Bool
  | .test, .test => true
  | .trial, .trial => true
  | .sReal _, .sReal _ => true
  | .mul a b, .mul c d => sameShape a c && sameShape b d
  | .inner a b, .inner c d => VectorExpr.sameShape a c && VectorExpr.sameShape b d
  | .pDeriv a _, .pDeriv b _ => VectorExpr.sameShape a b
  | _, _ => false

noncomputable def TopLevel.denote {dim : Nat}
    (e : TopLevel dim)
    (basis : Fin (dim + 1) -> MvPolynomial (Fin dim) Realish)
    (domain : Set (Fin dim -> Real)) :
    Fin (dim + 1) -> Fin (dim + 1) -> MvPolynomial (Fin dim) Realish :=
  match e with
  | Integral e => e.denote basis
  | Coeff r e => fun i j => MvPolynomial.C r * e.denote basis i j
  | Sum e1 e2 => fun i j =>
      e1.denote basis domain i j +
      e2.denote basis domain i j
