/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.Assembly

/-! # Semantic preservation for composed forms and assembly (Section 6.8). -/

/-- Quadrature semantics of top-level sums and coefficients. -/
def TopLevel.quadrature {dim nq : Nat} (f : TopLevel dim) (q : RatQuadScheme dim nq)
    (basis : Fin nq -> Fin (dim + 1) -> Realish) (detJ : Realish)
    (grads : Fin nq -> Fin (dim + 1) -> Fin dim -> Realish) (i j : Fin (dim + 1)) :
    Realish :=
  match f with
  | .Integral e => Finset.univ.sum fun g =>
      detJ * q.wts g * e.sample (basis g) (grads g) i j
  | .Coeff c e => c * Finset.univ.sum fun g =>
      detJ * q.wts g * e.sample (basis g) (grads g) i j
  | .Sum a b => a.quadrature q basis detJ grads i j + b.quadrature q basis detJ grads i j

/-- Paper lemma "Applying Top-Level Operations": compiling a form flattens its sums
and coefficients without changing the denotation of any local matrix entry. -/
theorem compileKernels_denote {dim nq : Nat} (f : TopLevel dim)
    (q : RatQuadScheme dim nq) (basis : Fin nq -> Fin (dim + 1) -> Realish)
    (ks : List (Prod Realish (MatrixKernel dim nq))) (h : compileKernels f q basis = some ks)
    (detJ : Realish) (grads : Fin nq -> Fin (dim + 1) -> Fin dim -> Realish)
    (i j : Fin (dim + 1)) :
    (ks.map (fun t => t.1 * t.2.denote detJ grads i j)).sum =
      f.quadrature q basis detJ grads i j := by
  induction f generalizing ks with
  | Integral e =>
      cases he : compileIntegral (rep := IrQuadType.denote) e q basis with
      | none => simp [compileKernels, he] at h
      | some k =>
          simp [compileKernels, he] at h
          cases h
          simpa [TopLevel.quadrature] using compileIntegral_denote e q basis k he detJ grads i j
  | Coeff c e =>
      cases he : compileIntegral (rep := IrQuadType.denote) e q basis with
      | none => simp [compileKernels, he] at h
      | some k =>
          simp [compileKernels, he] at h
          cases h
          simp [TopLevel.quadrature, compileIntegral_denote e q basis k he detJ grads i j]
  | Sum a b ia ib =>
      cases ha : compileKernels (rep := IrQuadType.denote) a q basis with
      | none => simp [compileKernels, ha] at h
      | some ka =>
          cases hb : compileKernels (rep := IrQuadType.denote) b q basis with
          | none => simp [compileKernels, ha, hb] at h
          | some kb =>
              simp [compileKernels, ha, hb] at h
              cases h
              simp [List.map_append, List.sum_append, ia ka ha, ib kb hb, TopLevel.quadrature]

/-- Paper lemma "Applying Top-Level Operations", for linear loads. -/
theorem compileLoadKernels_denote {dim nq : Nat} (f : TopLevel dim)
    (q : RatQuadScheme dim nq) (basis : Fin nq -> Fin (dim + 1) -> Realish)
    (ks : List (Prod Realish (VectorKernel dim nq)))
    (h : compileLoadKernels f q basis = some ks)
    (detJ : Realish) (grads : Fin nq -> Fin (dim + 1) -> Fin dim -> Realish)
    (i : Fin (dim + 1)) :
    (ks.map (fun t => t.1 * t.2.denote detJ grads i)).sum =
      f.quadrature q basis detJ grads i i := by
  induction f generalizing ks with
  | Integral e =>
      cases he : compileLinear (rep := IrQuadType.denote) e q basis with
      | none => simp [compileLoadKernels, he] at h
      | some k =>
          simp [compileLoadKernels, he] at h
          cases h
          simpa [TopLevel.quadrature] using compileLinear_denote e q basis k he detJ grads i
  | Coeff c e =>
      cases he : compileLinear (rep := IrQuadType.denote) e q basis with
      | none => simp [compileLoadKernels, he] at h
      | some k =>
          simp [compileLoadKernels, he] at h
          cases h
          simp [TopLevel.quadrature, compileLinear_denote e q basis k he detJ grads i]
  | Sum a b ia ib =>
      cases ha : compileLoadKernels (rep := IrQuadType.denote) a q basis with
      | none => simp [compileLoadKernels, ha] at h
      | some ka =>
          cases hb : compileLoadKernels (rep := IrQuadType.denote) b q basis with
          | none => simp [compileLoadKernels, ha, hb] at h
          | some kb =>
              simp [compileLoadKernels, ha, hb] at h
              cases h
              simp [List.map_append, List.sum_append, ia ka ha, ib kb hb, TopLevel.quadrature]

private theorem foldCodeObserve {n : Nat} {A : Type}
    (xs : List A) (step : ImpExpr ImpType.denote (.system n) -> A ->
      ImpExpr ImpType.denote (.system n)) (observe : FEMSystem n -> Realish) (f : A -> Realish)
    (h : forall code a, observe (step code a).denote = observe code.denote + f a)
    (code : ImpExpr ImpType.denote (.system n)) :
    observe (xs.foldl step code).denote = observe code.denote + (xs.map f).sum := by
  induction xs generalizing code with
  | nil => simp
  | cons a xs ih => simp [List.foldl_cons, ih, h, add_assoc]

/-- Paper theorem "Denotational Equivalence of Scatter-Add Code": actual kernel
application, coefficients, and scatter-add preserve the matrix specification. -/
theorem elementAssembly_matrix {dim nq n : Nat} (init : ImpExpr ImpType.denote (.system n))
    (vertices : Fin (dim + 1) -> Fin n) (detJ : Realish)
    (grads : Fin nq -> Fin (dim + 1) -> Fin dim -> Realish)
    (matrix : List (Prod Realish (ImpExpr ImpType.denote (.func dim nq))))
    (load : List (Prod Realish (ImpExpr ImpType.denote (.linearFunc dim nq))))
    (i j : Fin n) :
    (elementAssembly init vertices detJ grads matrix load).denote.1 i j =
      init.denote.1 i j + (matrix.map (fun t =>
        t.1 * scatterMatrixSpec vertices (t.2.denote detJ grads) i j)).sum := by
  unfold elementAssembly
  rw [foldCodeObserve (observe := fun s => s.1 i j) (f := fun _ => 0)]
  . simp only [List.map_const', List.sum_replicate, nsmul_zero, add_zero]
    rw [foldCodeObserve (observe := fun s => s.1 i j)
      (f := fun t => t.1 * scatterMatrixSpec vertices (t.2.denote detJ grads) i j)]
    intro code t
    exact scatterMatrix_denote code.denote vertices (t.2.denote detJ grads) t.1 i j
  . intro code t
    simp only [ImpExpr.denote, add_zero]
    exact congrFun (congrFun (scatterLoad_matrix code.denote vertices
      (t.2.denote detJ grads) t.1) i) j

/-- Paper theorem "Denotational Equivalence of Scatter-Add Code", actual load kernels. -/
theorem elementAssembly_load {dim nq n : Nat} (init : ImpExpr ImpType.denote (.system n))
    (vertices : Fin (dim + 1) -> Fin n) (detJ : Realish)
    (grads : Fin nq -> Fin (dim + 1) -> Fin dim -> Realish)
    (matrix : List (Prod Realish (ImpExpr ImpType.denote (.func dim nq))))
    (load : List (Prod Realish (ImpExpr ImpType.denote (.linearFunc dim nq))))
    (i : Fin n) :
    (elementAssembly init vertices detJ grads matrix load).denote.2 i =
      init.denote.2 i + (load.map (fun t =>
        t.1 * scatterLoadSpec vertices (t.2.denote detJ grads) i)).sum := by
  unfold elementAssembly
  rw [foldCodeObserve (observe := fun s => s.2 i)
    (f := fun t => t.1 * scatterLoadSpec vertices (t.2.denote detJ grads) i)]
  . rw [foldCodeObserve (observe := fun s => s.2 i) (f := fun _ => 0)]
    . simp
    . intro code t
      simp only [ImpExpr.denote, add_zero]
      exact congrFun (scatterMatrix_load code.denote vertices (t.2.denote detJ grads) t.1) i
  . intro code t
    exact scatterLoad_denote code.denote vertices (t.2.denote detJ grads) t.1 i

/-- Paper theorem "Semantics-Preserving FEM compilation in CertFEM": the lowered
matrix kernel denotes the sampled weak form for every Jacobian and physical gradient input. -/
theorem compileIntegral_toImp_denote {dim nq : Nat} (e : ScalarExpr dim)
    (q : RatQuadScheme dim nq) (basis : Fin nq -> Fin (dim + 1) -> Realish)
    (k : MatrixKernel dim nq) (h : compileIntegral e q basis = some k)
    (detJ : Realish) (grads : Fin nq -> Fin (dim + 1) -> Fin dim -> Realish)
    (i j : Fin (dim + 1)) :
    k.toImp.denote detJ grads i j = Finset.univ.sum (fun g =>
      detJ * q.wts g * e.sample (basis g) (grads g) i j) := by
  rw [QuadExpr.toImp_denote]
  exact compileIntegral_denote e q basis k h detJ grads i j

/-- Paper theorem "Semantics-Preserving FEM compilation in CertFEM", lowered load kernels. -/
theorem compileLinear_toImp_denote {dim nq : Nat} (e : ScalarExpr dim)
    (q : RatQuadScheme dim nq) (basis : Fin nq -> Fin (dim + 1) -> Realish)
    (k : VectorKernel dim nq) (h : compileLinear e q basis = some k)
    (detJ : Realish) (grads : Fin nq -> Fin (dim + 1) -> Fin dim -> Realish)
    (i : Fin (dim + 1)) :
    k.toImp.denote detJ grads i = Finset.univ.sum (fun g =>
      detJ * q.wts g * e.sample (basis g) (grads g) i i) := by
  rw [QuadExpr.toImp_denote]
  exact compileLinear_denote e q basis k h detJ grads i

/-- Sampling vector syntax agrees with its polynomial denotation on reference data. -/
theorem VectorExpr.sample_denote {dim : Nat} (e : VectorExpr dim) (basis : P1Basis dim)
    (x : Fin dim -> Realish) (i j : Fin (dim + 1)) (k : Fin dim) :
    e.sample (fun a => MvPolynomial.eval x (basis a))
      (fun a l => MvPolynomial.eval x (MvPolynomial.pderiv l (basis a))) i j k =
      MvPolynomial.eval x (e.denote basis i j k) := by
  induction e generalizing k with
  | gradTest | gradTrial | velVec => simp [VectorExpr.sample, VectorExpr.denote]
  | matMul D e ih =>
      simp [VectorExpr.sample, VectorExpr.denote, ih, MvPolynomial.eval_sum]

/-- Sampling scalar syntax agrees with its polynomial denotation on reference data. -/
theorem ScalarExpr.sample_denote {dim : Nat} (e : ScalarExpr dim) (basis : P1Basis dim)
    (x : Fin dim -> Realish) (i j : Fin (dim + 1)) :
    e.sample (fun a => MvPolynomial.eval x (basis a))
      (fun a l => MvPolynomial.eval x (MvPolynomial.pderiv l (basis a))) i j =
      MvPolynomial.eval x (e.denote basis i j) := by
  induction e with
  | test | trial | sReal => simp [ScalarExpr.sample, ScalarExpr.denote]
  | mul a b ia ib => simp [ScalarExpr.sample, ScalarExpr.denote, ia, ib]
  | inner a b =>
      simp [ScalarExpr.sample, ScalarExpr.denote, VectorExpr.sample_denote, MvPolynomial.eval_sum]
  | pDeriv a k => exact VectorExpr.sample_denote a basis x i j k

/-- Rational polynomial evaluation embeds into the real polynomial semantics exactly. -/
lemma evalPoly_rat {dim : Nat} (p : MvPolynomial (Fin dim) Realish) (x : Fin dim -> Realish) :
    evalPoly p (fun k => (x k : Real)) = (MvPolynomial.eval x p : Real) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [evalPoly]
  | add p q hp hq => simp_all [evalPoly]
  | mul_X p n hp =>
      simpa [evalPoly] using congrArg (fun a : Real => a * (x n : Real)) hp


/-- Paper theorem "Semantics-Preserving FEM compilation in CertFEM", reference
integral-to-lowered-kernel clause. Quadrature exactness is an explicit hypothesis;
rounded rules instead satisfy the error bounds in Approximation.lean. -/
theorem compileIntegral_exact {dim nq : Nat} (e : ScalarExpr dim) (basis : P1Basis dim)
    (q : RatQuadScheme dim nq) (maxDegree : Nat) (hq : QuadExact q.toReal maxDegree)
    (i j : Fin (dim + 1)) (hdegree : (e.denote basis i j).totalDegree <= maxDegree)
    (k : MatrixKernel dim nq)
    (hk : compileIntegral e q (fun g a => MvPolynomial.eval (q.pts g) (basis a)) = some k)
    (detJ : Realish) :
    (k.toImp.denote detJ
      (fun g a l => MvPolynomial.eval (q.pts g) (MvPolynomial.pderiv l (basis a))) i j : Real) =
        (detJ : Real) * exactPolyIntegral (e.denote basis i j) := by
  rw [compileIntegral_toImp_denote e q _ k hk]
  simp_rw [ScalarExpr.sample_denote]
  push_cast
  have he := hq (e.denote basis i j) hdegree
  rw [<- he]
  simp only [quadSum, RatQuadScheme.toReal, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [evalPoly_rat]
  ring

private theorem scatterMatrixSpec_list {n m : Nat} (vertices : Fin m -> Fin n)
    (ks : List (Prod Realish (Fin m -> Fin m -> Realish))) (i j : Fin n) :
    scatterMatrixSpec vertices (fun a b => (ks.map (fun t => t.1 * t.2 a b)).sum) i j =
      (ks.map (fun t => t.1 * scatterMatrixSpec vertices t.2 i j)).sum := by
  induction ks with
  | nil => simp [scatterMatrixSpec]
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [scatterMatrixSpec_add, scatterMatrixSpec_scale, ih]

private theorem scatterLoadSpec_scale {n m : Nat} (vertices : Fin m -> Fin n)
    (cell : Fin m -> Realish) (c : Realish) (i : Fin n) :
    scatterLoadSpec vertices (fun a => c * cell a) i = c * scatterLoadSpec vertices cell i := by
  simp [scatterLoadSpec, Finset.mul_sum, mul_ite]

private theorem scatterLoadSpec_add {n m : Nat} (vertices : Fin m -> Fin n)
    (a b : Fin m -> Realish) (i : Fin n) :
    scatterLoadSpec vertices (fun x => a x + b x) i =
      scatterLoadSpec vertices a i + scatterLoadSpec vertices b i := by
  simp only [scatterLoadSpec]
  simp_rw [ite_add_zero, Finset.sum_add_distrib]

private theorem scatterLoadSpec_list {n m : Nat} (vertices : Fin m -> Fin n)
    (ks : List (Prod Realish (Fin m -> Realish))) (i : Fin n) :
    scatterLoadSpec vertices (fun a => (ks.map (fun t => t.1 * t.2 a)).sum) i =
      (ks.map (fun t => t.1 * scatterLoadSpec vertices t.2 i)).sum := by
  induction ks with
  | nil => simp [scatterLoadSpec]
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [scatterLoadSpec_add, scatterLoadSpec_scale, ih]

/-- Paper theorem "Semantics-Preserving FEM compilation in CertFEM": compilation,
kernel application, top-level operations, and element scatter-add agree with the form's
quadrature semantics. The initial matrix and load can already contain other cells. -/
theorem compiledElement_denote {dim nq n : Nat} (lhs rhs : TopLevel dim)
    (q : RatQuadScheme dim nq) (basis : Fin nq -> Fin (dim + 1) -> Realish)
    (matrix : List (Prod Realish (MatrixKernel dim nq)))
    (load : List (Prod Realish (VectorKernel dim nq)))
    (hm : compileKernels lhs q basis = some matrix)
    (hl : compileLoadKernels rhs q basis = some load)
    (s : FEMSystem n) (vertices : Fin (dim + 1) -> Fin n) (detJ : Realish)
    (grads : Fin nq -> Fin (dim + 1) -> Fin dim -> Realish) :
    (elementAssembly (.var s) vertices detJ grads
      (matrix.map (fun t => (t.1, t.2.toImp)))
      (load.map (fun t => (t.1, t.2.toImp)))).denote =
      (fun i j => s.1 i j + scatterMatrixSpec vertices (lhs.quadrature q basis detJ grads) i j,
       fun i => s.2 i + scatterLoadSpec vertices (fun a => rhs.quadrature q basis detJ grads a a) i) := by
  apply Prod.ext
  . funext i j
    rw [elementAssembly_matrix]
    simp only [List.map_map, Function.comp_def, QuadExpr.toImp_denote, ImpExpr.denote]
    have hlocal :
        (fun a b => (matrix.map (fun t => t.1 * t.2.denote detJ grads a b)).sum) =
        lhs.quadrature q basis detJ grads := by
      funext a b
      exact compileKernels_denote lhs q basis matrix hm detJ grads a b
    rw [<- hlocal]
    have hscatter := scatterMatrixSpec_list vertices
      (matrix.map (fun t => (t.1, t.2.denote detJ grads))) i j
    simpa only [List.map_map, Function.comp_def] using congrArg (fun x => s.1 i j + x) hscatter.symm
  . funext i
    rw [elementAssembly_load]
    simp only [List.map_map, Function.comp_def, QuadExpr.toImp_denote, ImpExpr.denote]
    have hlocal : (fun a => (load.map (fun t => t.1 * t.2.denote detJ grads a)).sum) =
        (fun a => rhs.quadrature q basis detJ grads a a) := by
      funext a
      exact compileLoadKernels_denote rhs q basis load hl detJ grads a
    rw [<- hlocal]
    have hscatter := scatterLoadSpec_list vertices
      (load.map (fun t => (t.1, t.2.denote detJ grads))) i
    simpa only [List.map_map, Function.comp_def] using congrArg (fun x => s.2 i + x) hscatter.symm

/-- Paper theorem "Semantics-Preserving FEM compilation in CertFEM", including
Lemma "Imposing Boundary Conditions" for the actual compiled element program. -/
theorem compiledElementBoundary_denote {dim nq n : Nat} (lhs rhs : TopLevel dim)
    (q : RatQuadScheme dim nq) (basis : Fin nq -> Fin (dim + 1) -> Realish)
    (matrix : List (Prod Realish (MatrixKernel dim nq)))
    (load : List (Prod Realish (VectorKernel dim nq)))
    (hm : compileKernels lhs q basis = some matrix)
    (hl : compileLoadKernels rhs q basis = some load)
    (s : FEMSystem n) (vertices : Fin (dim + 1) -> Fin n) (detJ : Realish)
    (grads : Fin nq -> Fin (dim + 1) -> Fin dim -> Realish) (bs : List (Fin n)) :
    (imposeBoundaryBulk (elementAssembly (.var s) vertices detJ grads
      (matrix.map (fun t => (t.1, t.2.toImp)))
      (load.map (fun t => (t.1, t.2.toImp)))) bs).denote =
      boundarySpec
        (fun i j => s.1 i j + scatterMatrixSpec vertices (lhs.quadrature q basis detJ grads) i j,
         fun i => s.2 i + scatterLoadSpec vertices
           (fun a => rhs.quadrature q basis detJ grads a a) i) bs := by
  rw [imposeBoundaryBulk_denote, compiledElement_denote lhs rhs q basis matrix load hm hl]

/-- A typed outer element loop, parameterized by connectivity and geometric kernel inputs.
Geometry generation is a separate obligation from assembly. -/
def assembleElements {rep : ImpType -> Type} {dim nq n ne : Nat}
    (init : ImpExpr rep (.system n)) (vertices : rep (.vec ne (.vec (dim + 1) (.nat n))))
    (detJs : rep (.vec ne .real))
    (grads : rep (.vec ne (.vec nq (.vec (dim + 1) (.vec dim .real)))))
    (matrix : List (Prod Realish (ImpExpr rep (.func dim nq))))
    (load : List (Prod Realish (ImpExpr rep (.linearFunc dim nq)))) :
    ImpExpr rep (.system n) :=
  .forL init fun e acc =>
    .letE (.idx (.var vertices) (.var e)) fun v =>
      .letE (.idx (.var detJs) (.var e)) fun det =>
        .letE (.idx (.var grads) (.var e)) fun grad =>
          elementAssembly (.var acc) v det grad matrix load

private theorem observeFold {S A : Type} (xs : List A) (step : S -> A -> S)
    (observe : S -> Realish) (f : A -> Realish)
    (h : forall s a, observe (step s a) = observe s + f a) (s : S) :
    observe (xs.foldl step s) = observe s + (xs.map f).sum := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih => simp [List.foldl_cons, ih, h, add_assoc]

private theorem sumFinRange {n : Nat} (f : Fin n -> Realish) :
    ((List.finRange n).map f).sum = Finset.univ.sum f := by
  rw [<- List.sum_toFinset f (List.nodup_finRange n), List.toFinset_finRange]

/-- Paper theorem "Semantics-Preserving FEM compilation in CertFEM": the whole typed
element loop computes the global stiffness matrix and load vector of the compiled forms. -/
theorem compiledMesh_denote {dim nq n ne : Nat} (lhs rhs : TopLevel dim)
    (q : RatQuadScheme dim nq) (basis : Fin nq -> Fin (dim + 1) -> Realish)
    (matrix : List (Prod Realish (MatrixKernel dim nq)))
    (load : List (Prod Realish (VectorKernel dim nq)))
    (hm : compileKernels lhs q basis = some matrix)
    (hl : compileLoadKernels rhs q basis = some load)
    (s : FEMSystem n) (vertices : Fin ne -> Fin (dim + 1) -> Fin n) (detJs : Fin ne -> Realish)
    (grads : Fin ne -> Fin nq -> Fin (dim + 1) -> Fin dim -> Realish) :
    (assembleElements (.var s) vertices detJs grads
      (matrix.map (fun t => (t.1, t.2.toImp)))
      (load.map (fun t => (t.1, t.2.toImp)))).denote =
      (fun i j => s.1 i j + Finset.univ.sum (fun e =>
         scatterMatrixSpec (vertices e) (lhs.quadrature q basis (detJs e) (grads e)) i j),
       fun i => s.2 i + Finset.univ.sum (fun e => scatterLoadSpec (vertices e)
         (fun a => rhs.quadrature q basis (detJs e) (grads e) a a) i)) := by
  apply Prod.ext
  . funext i j
    unfold assembleElements
    simp only [ImpExpr.denote]
    rw [observeFold (observe := fun state : FEMSystem n => state.1 i j)
      (f := fun e => scatterMatrixSpec (vertices e)
        (lhs.quadrature q basis (detJs e) (grads e)) i j)]
    . rw [sumFinRange]
    . intro state e
      rw [compiledElement_denote lhs rhs q basis matrix load hm hl]
  . funext i
    unfold assembleElements
    simp only [ImpExpr.denote]
    rw [observeFold (observe := fun state : FEMSystem n => state.2 i)
      (f := fun e => scatterLoadSpec (vertices e)
        (fun a => rhs.quadrature q basis (detJs e) (grads e) a a) i)]
    . rw [sumFinRange]
    . intro state e
      rw [compiledElement_denote lhs rhs q basis matrix load hm hl]

/-- Paper theorem "Semantics-Preserving FEM compilation in CertFEM", global system
including simultaneous homogeneous Dirichlet elimination. This theorem concerns exact
Imp_FEM semantics; approximation bounds and the C/PETSc runtime are separate layers. -/
theorem compiledSystem_denote {dim nq n ne : Nat} (lhs rhs : TopLevel dim)
    (q : RatQuadScheme dim nq) (basis : Fin nq -> Fin (dim + 1) -> Realish)
    (matrix : List (Prod Realish (MatrixKernel dim nq)))
    (load : List (Prod Realish (VectorKernel dim nq)))
    (hm : compileKernels lhs q basis = some matrix)
    (hl : compileLoadKernels rhs q basis = some load)
    (s : FEMSystem n) (vertices : Fin ne -> Fin (dim + 1) -> Fin n) (detJs : Fin ne -> Realish)
    (grads : Fin ne -> Fin nq -> Fin (dim + 1) -> Fin dim -> Realish) (bs : List (Fin n)) :
    (imposeBoundaryBulk (assembleElements (.var s) vertices detJs grads
      (matrix.map (fun t => (t.1, t.2.toImp)))
      (load.map (fun t => (t.1, t.2.toImp)))) bs).denote =
      boundarySpec
        (fun i j => s.1 i j + Finset.univ.sum (fun e =>
           scatterMatrixSpec (vertices e) (lhs.quadrature q basis (detJs e) (grads e)) i j),
         fun i => s.2 i + Finset.univ.sum (fun e => scatterLoadSpec (vertices e)
           (fun a => rhs.quadrature q basis (detJs e) (grads e) a a) i)) bs := by
  rw [imposeBoundaryBulk_denote, compiledMesh_denote lhs rhs q basis matrix load hm hl]
