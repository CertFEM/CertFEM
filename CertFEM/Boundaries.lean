/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.Imp

/-! # Homogeneous Dirichlet elimination (Section 6.8). -/

/-- Dirichlet row-elimination spec. -/
def boundarySpec {n : Nat} (s : FEMSystem n) (boundary : List (Fin n)) : FEMSystem n :=
  (fun i j => if i = j /\ Membership.mem boundary i then 1
    else if Membership.mem boundary i \/ Membership.mem boundary j then 0 else s.1 i j,
   fun i => if Membership.mem boundary i then 0 else s.2 i)

/-- Imp_FEM snippet to impose Dirichlet at every selected vertex. -/
def imposeBoundary {rep : ImpType -> Type} {n : Nat}
    (s : ImpExpr rep (.system n)) (boundary : List (Fin n)) : ImpExpr rep (.system n) :=
  boundary.foldl (fun code b => .letE code fun acc => .dirichlet acc (.natLit b)) s

private theorem boundarySpec_cons {n : Nat} (s : FEMSystem n) (b : Fin n)
    (bs : List (Fin n)) :
    boundarySpec ((ImpExpr.dirichlet s (.natLit b)).denote) bs =
      boundarySpec s (b :: bs) := by
  apply Prod.ext
  . funext i j
    by_cases hij : i = j <;> by_cases hi : i = b <;> by_cases hj : j = b <;>
      by_cases hib : Membership.mem bs i <;> by_cases hjb : Membership.mem bs j <;>
      simp_all [boundarySpec, ImpExpr.denote]
  . funext i
    by_cases hi : i = b <;> by_cases hib : Membership.mem bs i <;>
      simp_all [boundarySpec, ImpExpr.denote, Function.update_apply]

/-- Paper lemma "Imposing Boundary Conditions": the generated Imp_FEM program
implements simultaneous row/column elimination, even for repeated boundary indices. -/
theorem imposeBoundary_denote {n : Nat} (s : ImpExpr ImpType.denote (.system n))
    (boundary : List (Fin n)) :
    (imposeBoundary s boundary).denote = boundarySpec s.denote boundary := by
  induction boundary generalizing s with
  | nil =>
      apply Prod.ext <;> funext i
      . funext j
        simp [imposeBoundary, boundarySpec]
      . simp [imposeBoundary, boundarySpec]
  | cons b bs ih =>
      rw [imposeBoundary, List.foldl_cons]
      change (imposeBoundary (.letE s fun acc => .dirichlet acc (.natLit b)) bs).denote = _
      rw [ih]
      exact boundarySpec_cons s.denote b bs

/-- Paper lemma "Imposing Boundary Conditions", interior matrix entries. -/
theorem imposeBoundary_interior {n : Nat} (s : FEMSystem n) (bs : List (Fin n))
    (i j : Fin n) (hi : Not (Membership.mem bs i)) (hj : Not (Membership.mem bs j)) :
    (imposeBoundary (.var s) bs).denote.1 i j = s.1 i j := by
  rw [imposeBoundary_denote]
  simp [boundarySpec, ImpExpr.denote, hi, hj]

/-- Paper lemma "Imposing Boundary Conditions", interior load entries. -/
theorem imposeBoundary_load_interior {n : Nat} (s : FEMSystem n) (bs : List (Fin n))
    (i : Fin n) (hi : Not (Membership.mem bs i)) :
    (imposeBoundary (.var s) bs).denote.2 i = s.2 i := by
  rw [imposeBoundary_denote]
  simp [boundarySpec, ImpExpr.denote, hi]

/-- Paper lemma "Imposing Boundary Conditions", unit boundary diagonal and zero load. -/
theorem imposeBoundary_diagonal {n : Nat} (s : FEMSystem n) (bs : List (Fin n))
    (b : Fin n) (hb : Membership.mem bs b) :
    (imposeBoundary (.var s) bs).denote.1 b b = 1 /\
      (imposeBoundary (.var s) bs).denote.2 b = 0 := by
  rw [imposeBoundary_denote]
  simp [boundarySpec, hb]

/-- Paper lemma "Imposing Boundary Conditions", off-diagonal boundary rows and columns. -/
theorem imposeBoundary_offDiagonal {n : Nat} (s : FEMSystem n) (bs : List (Fin n))
    (b i : Fin n) (hb : Membership.mem bs b) (hi : i = b -> False) :
    (imposeBoundary (.var s) bs).denote.1 b i = 0 /\
      (imposeBoundary (.var s) bs).denote.1 i b = 0 := by
  rw [imposeBoundary_denote]
  simp_all [boundarySpec, Ne.symm hi]

/-- Bulk boundary elimination, emitted as one sparse PETSc operation. -/
def imposeBoundaryBulk {rep : ImpType -> Type} {n : Nat}
    (s : ImpExpr rep (.system n)) (boundary : List (Fin n)) : ImpExpr rep (.system n) :=
  .letE s fun acc => .dirichletMany acc boundary

/-- Paper lemma "Imposing Boundary Conditions", bulk runtime primitive. -/
theorem imposeBoundaryBulk_denote {n : Nat} (s : ImpExpr ImpType.denote (.system n))
    (boundary : List (Fin n)) :
    (imposeBoundaryBulk s boundary).denote = boundarySpec s.denote boundary := by
  have hfold : (imposeBoundary s boundary).denote =
      boundary.foldl (fun state b => (ImpExpr.dirichlet state (.natLit b)).denote)
        s.denote := by
    induction boundary generalizing s with
    | nil => rfl
    | cons b bs ih =>
        exact ih (.letE s fun acc => .dirichlet acc (.natLit b))
  rw [<- imposeBoundary_denote s boundary, hfold]
  rfl
