/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.IRQuad
import CertFEM.DefPCI
import CertFEM.Duffy
import CertFEM.Approximation
import CertFEM.Mesh
import CertFEM.Boundaries

/-! # Assembly and semantics-preserving lowering (Sections 5 and 6.7-6.8). -/

/-! ## Lowering IR_QUAD to Imp_FEM -/

/-- Lower an IR_QUAD expression to Imp. -/
def QuadExpr.toImp {rep : ImpType -> Type} {ty : IrQuadType}
    (e : QuadExpr (fun t => rep (quadTypeToImp t)) ty) :
    ImpExpr rep (quadTypeToImp ty) :=
  match e with
  | .var x => .var x
  | .const x => .scalar x
  | .natLit i => .natLit i
  | .vecLit xs => .vecOf (fun i => (xs i).toImp)
  | .mul a b => .mul a.toImp b.toImp
  | .summ f => .forL (.scalar 0) fun i acc => .add (.var acc) (f i).toImp
  | .map f =>
      .forL (.vecOf (fun _ => .vecOf (fun _ => .scalar 0))) fun i rows =>
        .arrAssign rows (.var i) <|
          .forL (.vecOf (fun _ => .scalar 0)) fun j row =>
            .arrAssign row (.var j) (f i j).toImp
  | .letE a f => .letE a.toImp (fun x => (f x).toImp)
  | .idx a i => .idx a.toImp i.toImp
  | .map1 f =>
      .forL (.vecOf (fun _ => .scalar 0)) fun i acc =>
        .arrAssign acc (.var i) (f i).toImp
  | .func f => .func (fun _ detJ grads => (f detJ grads).toImp)
  | .linearFunc f => .linearFunc (fun _ detJ grads => (f detJ grads).toImp)

def quadToImp {dim nq : Nat}
    (e : QuadExpr IrQuadType.denote (QuadFuncType nq dim)) :
    ImpExpr ImpType.denote (.func dim nq) :=
  e.toImp

private theorem foldlAdd {alpha : Type} (xs : List alpha) (f : alpha -> Realish) (acc : Realish) :
    xs.foldl (fun acc x => acc + f x) acc = acc + (xs.map f).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih => simp [ih, add_assoc]

private theorem foldlFinSum {n : Nat} (f : Fin n -> Realish) :
    (List.finRange n).foldl (fun acc i => acc + f i) 0 = Finset.univ.sum f := by
  rw [foldlAdd, zero_add, <- List.sum_toFinset f (List.nodup_finRange n), List.toFinset_finRange]

private theorem foldlUpdate {alpha beta : Type} [DecidableEq alpha]
    (xs : List alpha) (f : alpha -> beta) (init : alpha -> beta) (i : alpha) :
    (xs.foldl (fun acc j => Function.update acc j (f j)) init) i =
      if Membership.mem xs i then f i else init i := by
  induction xs generalizing init with
  | nil => simp
  | cons a xs ih =>
      rw [List.foldl_cons, ih]
      by_cases h : Membership.mem xs i
      . simp [h]
      . by_cases hij : i = a
        . subst a
          simp [h]
        . simp [h, hij, Function.update_of_ne]

private theorem foldlFinMap {n : Nat} {beta : Type} (f init : Fin n -> beta) :
    (List.finRange n).foldl (fun acc j => Function.update acc j (f j)) init = f := by
  funext i
  rw [foldlUpdate, if_pos (List.mem_finRange i)]

/-- Paper theorem "Semantics-Preserving FEM compilation in CertFEM": the
IR_QUAD-to-Imp_FEM clauses hold for every expression and all kernel inputs. -/
theorem QuadExpr.toImp_denote {ty : IrQuadType} (e : QuadExpr IrQuadType.denote ty) :
    e.toImp.denote = e.denote := by
  induction e with
  | var | const | natLit => rfl
  | vecLit xs ih => simp [toImp, ImpExpr.denote, denote, ih]
  | mul a b ha hb => simp [toImp, ImpExpr.denote, denote, ha, hb]
  | summ f ih => simp [toImp, ImpExpr.denote, denote, ih, foldlFinSum]
  | map f ih => simp [toImp, ImpExpr.denote, denote, ih, foldlFinMap]
  | letE a f ha hf => simp [toImp, ImpExpr.denote, denote, ha, hf]
  | idx a i ha hi => simp [toImp, ImpExpr.denote, denote, ha, hi]
  | map1 f ih => simp [toImp, ImpExpr.denote, denote, ih, foldlFinMap]
  | func f ih => simp [toImp, ImpExpr.denote, denote, ih]
  | linearFunc f ih => simp [toImp, ImpExpr.denote, denote, ih]

/-! ## Sparse scatter-add programs -/

/-- Scatter one cell matrix using Imp_FEM loops and sparse matrix additions. -/
def scatterMatrix {rep : ImpType -> Type} {n m : Nat}
    (s : ImpExpr rep (.system n)) (vertices : rep (.vec m (.nat n)))
    (cell : rep (.vec m (.vec m .real))) (scale : Realish) :
    ImpExpr rep (.system n) :=
  .forL s fun i rows =>
    .forL (.var rows) fun j acc =>
      .matrixAdd acc (.idx (.var vertices) (.var i)) (.idx (.var vertices) (.var j))
        (.mul (.scalar scale) (.idx (.idx (.var cell) (.var i)) (.var j)))

/-- Scatter one cell load using Imp_FEM loops and sparse vector additions. -/
def scatterLoad {rep : ImpType -> Type} {n m : Nat}
    (s : ImpExpr rep (.system n)) (vertices : rep (.vec m (.nat n)))
    (cell : rep (.vec m .real)) (scale : Realish) : ImpExpr rep (.system n) :=
  .forL s fun i acc =>
    .loadAdd acc (.idx (.var vertices) (.var i))
      (.mul (.scalar scale) (.idx (.var cell) (.var i)))

/-- The entries of S k S^T, allowing repeated indices in the connectivity map. -/
def scatterMatrixSpec {n m : Nat} (vertices : Fin m -> Fin n)
    (cell : Fin m -> Fin m -> Realish) (i j : Fin n) : Realish :=
  Finset.univ.sum fun a => Finset.univ.sum fun b =>
    if vertices a = i /\ vertices b = j then cell a b else 0

def scatterLoadSpec {n m : Nat} (vertices : Fin m -> Fin n)
    (cell : Fin m -> Realish) (i : Fin n) : Realish :=
  Finset.univ.sum fun a => if vertices a = i then cell a else 0

private theorem foldlObserve {S A R : Type} [AddCommMonoid R]
    (xs : List A) (step : S -> A -> S) (observe : S -> R) (f : A -> R)
    (h : forall s a, observe (step s a) = observe s + f a) (s : S) :
    observe (xs.foldl step s) = observe s + (xs.map f).sum := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih => simp [ih, h, add_assoc]

private theorem finRangeSum {R : Type} [AddCommMonoid R] {n : Nat} (f : Fin n -> R) :
    ((List.finRange n).map f).sum = Finset.univ.sum f := by
  rw [<- List.sum_toFinset f (List.nodup_finRange n), List.toFinset_finRange]

/-- Paper theorem "Denotational Equivalence of Scatter-Add Code", matrix clause.
The proof covers arbitrary initial matrices, connectivity, coefficients, and duplicate indices. -/
theorem scatterMatrix_denote {n m : Nat} (s : FEMSystem n)
    (vertices : Fin m -> Fin n) (cell : Fin m -> Fin m -> Realish)
    (scale : Realish) (i j : Fin n) :
    (scatterMatrix (.var s) vertices cell scale).denote.1 i j =
      s.1 i j + scale * scatterMatrixSpec vertices cell i j := by
  classical
  unfold scatterMatrix
  simp only [ImpExpr.denote]
  rw [foldlObserve (observe := fun s : FEMSystem n => s.1 i j)
    (f := fun a => Finset.univ.sum fun b =>
      if vertices a = i /\ vertices b = j then scale * cell a b else 0)]
  . rw [finRangeSum]
    simp [scatterMatrixSpec, Finset.mul_sum, mul_ite]
  . intro acc a
    rw [foldlObserve (observe := fun s : FEMSystem n => s.1 i j)
      (f := fun b => if vertices a = i /\ vertices b = j then scale * cell a b else 0)]
    . rw [finRangeSum]
    . intro state b
      by_cases hi : vertices a = i <;> by_cases hj : vertices b = j <;>
        simp_all [ImpExpr.denote, Function.update_apply, eq_comm]

/-- Scatter-add leaves the load vector unchanged. -/
theorem scatterMatrix_load {n m : Nat} (s : FEMSystem n)
    (vertices : Fin m -> Fin n) (cell : Fin m -> Fin m -> Realish) (scale : Realish) :
    (scatterMatrix (.var s) vertices cell scale).denote.2 = s.2 := by
  unfold scatterMatrix
  simp only [ImpExpr.denote]
  have preserve {A : Type} (xs : List A) (step : FEMSystem n -> A -> FEMSystem n)
      (h : forall s a, (step s a).2 = s.2) (s : FEMSystem n) :
      (xs.foldl step s).2 = s.2 := by
    induction xs generalizing s with
    | nil => rfl
    | cons a xs ih => simpa [List.foldl_cons, h] using ih (step s a)
  apply preserve
  intro acc a
  apply preserve
  intro state b
  rfl

/-- Paper theorem "Denotational Equivalence of Scatter-Add Code", load clause. -/
theorem scatterLoad_denote {n m : Nat} (s : FEMSystem n)
    (vertices : Fin m -> Fin n) (cell : Fin m -> Realish)
    (scale : Realish) (i : Fin n) :
    (scatterLoad (.var s) vertices cell scale).denote.2 i =
      s.2 i + scale * scatterLoadSpec vertices cell i := by
  classical
  unfold scatterLoad
  simp only [ImpExpr.denote]
  rw [foldlObserve (observe := fun s : FEMSystem n => s.2 i)
    (f := fun a => if vertices a = i then scale * cell a else 0)]
  . rw [finRangeSum]
    simp [scatterLoadSpec, Finset.mul_sum, mul_ite]
  . intro acc a
    by_cases h : vertices a = i <;> simp_all [ImpExpr.denote, Function.update_apply, eq_comm]

/-- Scatter-add leaves the stiffness matrix unchanged when adding a load. -/
theorem scatterLoad_matrix {n m : Nat} (s : FEMSystem n)
    (vertices : Fin m -> Fin n) (cell : Fin m -> Realish) (scale : Realish) :
    (scatterLoad (.var s) vertices cell scale).denote.1 = s.1 := by
  unfold scatterLoad
  simp only [ImpExpr.denote]
  generalize List.finRange m = xs
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih =>
      simpa only [List.foldl_cons] using ih
        (s.1, Function.update s.2 (vertices a) (s.2 (vertices a) + scale * cell a))

/-- Assemble a mesh's cell matrices in Imp_FEM, with one state threaded through all cells. -/
def assembleMatrices {rep : ImpType -> Type} {n m ne : Nat}
    (s : ImpExpr rep (.system n)) (vertices : rep (.vec ne (.vec m (.nat n))))
    (cell : rep (.vec ne (.vec m (.vec m .real)))) : ImpExpr rep (.system n) :=
  .forL s fun e acc =>
    .letE (.idx (.var vertices) (.var e)) fun v =>
      .letE (.idx (.var cell) (.var e)) fun k => scatterMatrix (.var acc) v k 1

/-- Paper theorem "Denotational Equivalence of Scatter-Add Code": the element loop
computes the sum of all S(e) k(e) S(e)^T contributions. -/
theorem assembleMatrices_denote {n m ne : Nat} (s : FEMSystem n)
    (vertices : Fin ne -> Fin m -> Fin n) (cell : Fin ne -> Fin m -> Fin m -> Realish)
    (i j : Fin n) :
    (assembleMatrices (.var s) vertices cell).denote.1 i j =
      s.1 i j + Finset.univ.sum (fun e => scatterMatrixSpec (vertices e) (cell e) i j) := by
  unfold assembleMatrices
  simp only [ImpExpr.denote]
  rw [foldlObserve (observe := fun s : FEMSystem n => s.1 i j)
    (f := fun e => scatterMatrixSpec (vertices e) (cell e) i j)]
  . rw [finRangeSum]
  . intro acc e
    simpa only [one_mul] using scatterMatrix_denote acc (vertices e) (cell e) 1 i j

/-- Paper lemma "Applying Top-Level Operations": scatter commutes with coefficients. -/
theorem scatterMatrixSpec_scale {n m : Nat} (vertices : Fin m -> Fin n)
    (cell : Fin m -> Fin m -> Realish) (c : Realish) (i j : Fin n) :
    scatterMatrixSpec vertices (fun a b => c * cell a b) i j =
      c * scatterMatrixSpec vertices cell i j := by
  simp [scatterMatrixSpec, Finset.mul_sum, mul_ite]

/-- Paper lemma "Applying Top-Level Operations": scatter commutes with summation. -/
theorem scatterMatrixSpec_add {n m : Nat} (vertices : Fin m -> Fin n)
    (a b : Fin m -> Fin m -> Realish) (i j : Fin n) :
    scatterMatrixSpec vertices (fun x y => a x y + b x y) i j =
      scatterMatrixSpec vertices a i j + scatterMatrixSpec vertices b i j := by
  simp only [scatterMatrixSpec]
  simp_rw [ite_add_zero]
  simp_rw [Finset.sum_add_distrib]

/-- Apply compiled kernels, coefficients, and sparse scatter-add inside an element loop. -/
def elementAssembly {rep : ImpType -> Type} {dim nq n : Nat}
    (init : ImpExpr rep (.system n)) (vertices : rep (.vec (dim + 1) (.nat n)))
    (detJ : rep .real) (grads : rep (.vec nq (.vec (dim + 1) (.vec dim .real))))
    (matrix : List (Prod Realish (ImpExpr rep (.func dim nq))))
    (load : List (Prod Realish (ImpExpr rep (.linearFunc dim nq)))) :
    ImpExpr rep (.system n) :=
  let matrixCode := matrix.foldl (fun code term =>
    .letE code fun acc => .letE term.2 fun kernel =>
      .letE (.app kernel detJ grads) fun cell =>
        scatterMatrix (.var acc) vertices cell term.1) init
  load.foldl (fun code term =>
    .letE code fun acc => .letE term.2 fun kernel =>
      .letE (.linearApp kernel detJ grads) fun cell =>
        scatterLoad (.var acc) vertices cell term.1) matrixCode

/-! ## Compile functions. -/

def compileIntegral {dim nq : Nat} {rep : IrQuadType -> Type}
    (e : ScalarExpr dim)
    (q : RatQuadScheme dim nq)
    (basisVals : Fin nq -> Fin (dim + 1) -> Realish)
    : Option (QuadExpr rep (QuadFuncType nq dim)) :=
  match e with
  | .mul .test .trial | .mul .trial .test =>
      some (massKernel q basisVals)
  | .inner .gradTest .gradTrial | .inner .gradTrial .gradTest =>
      some (diffusionKernel q basisVals)
  | .inner .gradTest (.matMul D .gradTrial) =>
      some (anisotropicDiffusionKernel q basisVals D)
  | .mul .test (.inner (.velVec beta) .gradTrial)
  | .mul (.inner (.velVec beta) .gradTrial) .test =>
      some (advectionKernel q basisVals beta)
  | .mul .test (.pDeriv .gradTrial dir)
  | .mul (.pDeriv .gradTrial dir) .test =>
      some (gradientKernel q basisVals dir)
  | _ =>
      none

def compileLinear {dim nq : Nat} {rep : IrQuadType -> Type}
    (e : ScalarExpr dim)
    (q : RatQuadScheme dim nq)
    (basisVals : Fin nq -> Fin (dim + 1) -> Realish)
    : Option (QuadExpr rep (LinearQuadFuncType nq dim)) :=
  match e with
  | .mul (.sReal f) .test | .mul .test (.sReal f) =>
      some (linearKernel q basisVals f)
  | _ =>
      none

def compileKernels {dim nq : Nat} {rep : IrQuadType -> Type}
    (f : TopLevel dim)
    (q : RatQuadScheme dim nq)
    (basisVals : Fin nq -> Fin (dim + 1) -> Realish)
    : Option (List (Prod Realish (QuadExpr rep (QuadFuncType nq dim)))) :=
  match f with
  | .Integral e => do
      let k <- compileIntegral e q basisVals
      return [(1, k)]
  | .Coeff r e => do
      let k <- compileIntegral e q basisVals
      return [(r, k)]
  | .Sum e1 e2 => do
      let ks1 <- compileKernels e1 q basisVals
      let ks2 <- compileKernels e2 q basisVals
      return ks1 ++ ks2

def compileLoadKernels {dim nq : Nat} {rep : IrQuadType -> Type}
    (f : TopLevel dim) (q : RatQuadScheme dim nq)
    (basisVals : Fin nq -> Fin (dim + 1) -> Realish) :
    Option (List (Prod Realish (QuadExpr rep (LinearQuadFuncType nq dim)))) :=
  match f with
  | .Integral e => (compileLinear e q basisVals).map fun k => [(1, k)]
  | .Coeff r e => (compileLinear e q basisVals).map fun k => [(r, k)]
  | .Sum a b => do
      let ka <- compileLoadKernels a q basisVals
      let kb <- compileLoadKernels b q basisVals
      return ka ++ kb

/-- Compiler settings. The tolerance bounds the absolute error of the one-dimensional
Gauss nodes before the Duffy transform. Generated C arithmetic remains floating-point. -/
structure CompilerOptions where
  quadratureTolerance : Realish := 1 / 100000000000000000

private def gaussNodes (tol : Realish) : Fin 3 -> Realish :=
  fun g => (approximateThreePt tol).pts g 0

private def gaussWeights : Fin 3 -> Realish := ![5 / 9, 8 / 9, 5 / 9]

private def solverQuadrature (dim : Nat) (tol : Realish) : RatQuadScheme dim (3 ^ dim) where
  pts g k :=
    let node := fun i => gaussNodes tol (finFunctionFinEquiv.symm g i)
    if dim = 1 then node k else
      ((1 + node k) / 2) * ((List.finRange dim).foldl (fun acc i =>
        if k < i then acc * ((1 - node i) / 2) else acc) 1)
  wts g :=
    let idx := finFunctionFinEquiv.symm g
    if h : dim = 1 then gaussWeights (idx (Fin.mk 0 (by omega))) else
      (List.finRange dim).foldl (fun acc i =>
        acc * (gaussWeights (idx i) / 2) * (((1 - gaussNodes tol (idx i)) / 2) ^ i.val)) 1

private def solverBasisValues {dim nq : Nat} (q : RatQuadScheme dim nq) :
    Fin nq -> Fin (dim + 1) -> Realish :=
  fun g =>
    let coord := fun i => if dim = 1 then (1 + q.pts g i) / 2 else q.pts g i
    Fin.cons (1 - (List.finRange dim).foldl (fun acc i => acc + coord i) 0) coord

/-- Compile the supported P1 weak forms and mesh to a sequential PETSc program. -/
def solveWithOptions {dim nv nt : Nat} (options : CompilerOptions)
    (lhs rhs : TopLevel dim) (m : Mesh dim nv nt) (bc : List (Fin nv))
    (filename : String) : Except String String := do
  unless 0 < options.quadratureTolerance do
    throw "Expected a positive quadrature tolerance"
  unless dim = 1 || dim = 2 do
    throw "Expected a one- or two-dimensional simplex mesh"
  unless nv > 0 && nt > 0 do
    throw "Expected a nonempty mesh"
  let q := solverQuadrature dim options.quadratureTolerance
  let basis := solverBasisValues q
  let some matrix := compileKernels (rep := fun ty => CRep (quadTypeToImp ty)) lhs q basis
    | throw "Unsupported left-hand side integrator"
  let some load := compileLoadKernels (rep := fun ty => CRep (quadTypeToImp ty)) rhs q basis
    | throw "Unsupported right-hand side integrator"
  let code := ImpExpr.letE (.vecLit (fun i : Fin (dim + 1) => s!"v[{i.val}]")) fun vertices =>
    elementAssembly (.var "system") vertices "detJ" "grads"
      (matrix.map fun (r, k) => (r, k.toImp)) (load.map fun (r, k) => (r, k.toImp))
  let boundary := imposeBoundaryBulk (.var "system") bc
  return emitAssembly (nq := 3 ^ dim) code boundary m.coords m.elements filename

/-- Compile with the default approximation tolerance. -/
def solve {dim nv nt : Nat} (lhs rhs : TopLevel dim) (m : Mesh dim nv nt)
    (bc : List (Fin nv)) (filename : String) : Except String String :=
  solveWithOptions {} lhs rhs m bc filename

/-! ## From form expressions to quadrature kernels -/

/-- Sample vector form syntax using basis values and physical gradients at one point. -/
def VectorExpr.sample {dim : Nat} (e : VectorExpr dim)
    (values : Fin (dim + 1) -> Realish) (grads : Fin (dim + 1) -> Fin dim -> Realish)
    (i j : Fin (dim + 1)) : Fin dim -> Realish :=
  match e with
  | .gradTest => grads i
  | .gradTrial => grads j
  | .velVec beta => beta
  | .matMul D v => fun k => Finset.univ.sum fun l => D k l * v.sample values grads i j l

/-- Sample scalar form syntax at one quadrature point. -/
def ScalarExpr.sample {dim : Nat} (e : ScalarExpr dim)
    (values : Fin (dim + 1) -> Realish) (grads : Fin (dim + 1) -> Fin dim -> Realish)
    (i j : Fin (dim + 1)) : Realish :=
  match e with
  | .test => values i
  | .trial => values j
  | .sReal c => c
  | .mul a b => a.sample values grads i j * b.sample values grads i j
  | .inner a b => Finset.univ.sum fun k =>
      a.sample values grads i j k * b.sample values grads i j k
  | .pDeriv a k => a.sample values grads i j k

/-- Paper theorem "Semantics-Preserving FEM compilation in CertFEM", bilinear
IR_FORM-to-IR_QUAD clause. The Jacobian and physical gradients are arbitrary inputs. -/
theorem compileIntegral_denote {dim nq : Nat} (e : ScalarExpr dim)
    (q : RatQuadScheme dim nq) (basis : Fin nq -> Fin (dim + 1) -> Realish)
    (k : MatrixKernel dim nq) (h : compileIntegral e q basis = some k)
    (detJ : Realish) (grads : Fin nq -> Fin (dim + 1) -> Fin dim -> Realish)
    (i j : Fin (dim + 1)) :
    k.denote detJ grads i j = Finset.univ.sum (fun g =>
      detJ * q.wts g * e.sample (basis g) (grads g) i j) := by
  unfold compileIntegral at h
  split at h <;> cases h
  all_goals simp [massKernel, diffusionKernel, anisotropicDiffusionKernel,
    advectionKernel, gradientKernel, QuadExpr.denote, ScalarExpr.sample, VectorExpr.sample,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Paper theorem "Semantics-Preserving FEM compilation in CertFEM", load
IR_FORM-to-IR_QUAD clause, for arbitrary Jacobian and gradient inputs. -/
theorem compileLinear_denote {dim nq : Nat} (e : ScalarExpr dim)
    (q : RatQuadScheme dim nq) (basis : Fin nq -> Fin (dim + 1) -> Realish)
    (k : VectorKernel dim nq) (h : compileLinear e q basis = some k)
    (detJ : Realish) (grads : Fin nq -> Fin (dim + 1) -> Fin dim -> Realish)
    (i : Fin (dim + 1)) :
    k.denote detJ grads i = Finset.univ.sum (fun g =>
      detJ * q.wts g * e.sample (basis g) (grads g) i i) := by
  unfold compileLinear at h
  split at h <;> cases h
  all_goals simp [linearKernel, QuadExpr.denote, ScalarExpr.sample,
    mul_assoc, mul_left_comm, mul_comm]
