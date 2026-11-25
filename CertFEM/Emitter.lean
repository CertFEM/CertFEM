/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.Util
import CertFEM.Imp

/-! # Imp_FEM C emitter -/

abbrev CRep (_ : ImpType) : Type := String

private abbrev matrixTy (dim : Nat) : ImpType :=
  .vec (dim + 1) (.vec (dim + 1) .real)

private abbrev linearTy (dim : Nat) : ImpType :=
  .vec (dim + 1) .real

private abbrev gradsTy (dim nq : Nat) : ImpType :=
  .vec nq (.vec (dim + 1) (.vec dim .real))

private def ImpType.cTag : ImpType -> String
  | .unit => "unit"
  | .real => "real"
  | .nat n => s!"nat{n}"
  | .vec n ty => s!"vec{n}_{ty.cTag}"
  | .func dim nq => s!"func{dim}_{nq}"
  | .linearFunc dim nq => s!"linearFunc{dim}_{nq}"
  | .system _ => "fem_system"

def ImpType.cType : ImpType -> String
  | .unit => "unsigned char"
  | .real => "double"
  | .nat _ => "size_t" -- was "int" in paper
  | ty => "T_" ++ ty.cTag

structure EmitState where
  nextId : Nat := 0
  typedefs : List String := []
  functions : List String := []

structure CResult where
  lines : List String
  value : String

private def addTypedef (decl : String) :
    StateM EmitState Unit := do
  let s <- get
  if !s.typedefs.contains decl then
    set { s with typedefs := s.typedefs ++ [decl] }

private partial def registerCType (ty : ImpType) :
    StateM EmitState Unit := do
  match ty with
  | .vec n elem =>
      registerCType elem
      addTypedef (
        "typedef struct { " ++ elem.cType ++
        " data[" ++ toString (max 1 n) ++
        "]; } " ++ ty.cType ++ ";")
  | .system _ =>
      addTypedef "typedef struct { Mat matrix; double *load; } T_fem_system;"
  | .func dim nq =>
      registerCType (matrixTy dim)
      registerCType (gradsTy dim nq)
      addTypedef (
        "typedef " ++ (matrixTy dim).cType ++
        " (*" ++ ty.cType ++ ")(double, " ++
        (gradsTy dim nq).cType ++ ");")
  | .linearFunc dim nq =>
      registerCType (linearTy dim)
      registerCType (gradsTy dim nq)
  | _ =>
      pure ()

private def indentLines (lines : List String) : List String :=
  lines.map (fun line => "  " ++ line)

private def freshName (base : String) : StateM EmitState String := do
  let s <- get
  set { s with nextId := s.nextId + 1 }
  return s!"{base}_{s.nextId}"

def solveFunc (dim : Nat) : StateM EmitState String := do
  let name <- freshName "solve"

  let code := r#"static PetscErrorCode SOLVER_NAME(
    PetscInt n, Mat A, const double b[n],
    PetscInt nt, const double coords[n][DIM],
    const PetscInt elements[nt][DIM + 1], const char *filename)
{
    Vec rhs, x; KSP ksp; PC pc; FILE *fp;
    const PetscScalar *xa;
    PetscFunctionBegin;

    PetscCall(MatAssemblyBegin(A, MAT_FINAL_ASSEMBLY));
    PetscCall(MatAssemblyEnd(A, MAT_FINAL_ASSEMBLY));

    PetscCall(VecCreateSeq(PETSC_COMM_SELF, n, &rhs));
    for (PetscInt i = 0; i < n; ++i)
        PetscCall(VecSetValue(rhs, i, b[i], INSERT_VALUES));

    PetscCall(VecAssemblyBegin(rhs));
    PetscCall(VecAssemblyEnd(rhs));
    PetscCall(VecDuplicate(rhs, &x));
    PetscCall(KSPCreate(PETSC_COMM_SELF, &ksp));
    PetscCall(KSPSetOperators(ksp, A, A));
    PetscCall(KSPSetType(ksp, KSPPREONLY));
    PetscCall(KSPGetPC(ksp, &pc));
    PetscCall(PCSetType(pc, PCLU));
    PetscCall(KSPSetErrorIfNotConverged(ksp, PETSC_TRUE));
    PetscCall(KSPSetFromOptions(ksp));
    PetscCall(KSPSolve(ksp, rhs, x));
    PetscCall(VecGetArrayRead(x, &xa));

    fp = fopen(filename, "w");
    PetscCheck(fp != NULL, PETSC_COMM_SELF, PETSC_ERR_FILE_OPEN,
               "Could not open %s", filename);

    fprintf(fp, "<?xml version=\"1.0\"?>\n");
    fprintf(fp, "<VTKFile type=\"UnstructuredGrid\" version=\"0.1\" byte_order=\"LittleEndian\">\n");
    fprintf(fp, "<UnstructuredGrid>\n");
    fprintf(fp, "<Piece NumberOfPoints=\"%lld\" NumberOfCells=\"%lld\">\n",
            (long long)n, (long long)nt);

    fprintf(fp, "<Points><DataArray type=\"Float64\" NumberOfComponents=\"3\" format=\"ascii\">\n");
    for (PetscInt i = 0; i < n; ++i) {
        for (PetscInt d = 0; d < DIM; ++d)
            fprintf(fp, "%.17g ", coords[i][d]);
        for (PetscInt d = DIM; d < 3; ++d)
            fprintf(fp, "0 ");
        fprintf(fp, "\n");
    }
    fprintf(fp, "</DataArray></Points>\n");

    fprintf(fp, "<Cells>\n");
    fprintf(fp, "<DataArray type=\"Int64\" Name=\"connectivity\" format=\"ascii\">\n");
    for (PetscInt e = 0; e < nt; ++e) {
        for (PetscInt j = 0; j < DIM + 1; ++j)
            fprintf(fp, "%lld ", (long long)elements[e][j]);
        fprintf(fp, "\n");
    }
    fprintf(fp, "</DataArray>\n");

    fprintf(fp, "<DataArray type=\"Int64\" Name=\"offsets\" format=\"ascii\">\n");
    for (PetscInt e = 0; e < nt; ++e)
        fprintf(fp, "%lld\n", (long long)(e + 1) * (DIM + 1));
    fprintf(fp, "</DataArray>\n");

    static const int vtkSimplexType[] = {1, 3, 5, 10};
    fprintf(fp, "<DataArray type=\"UInt8\" Name=\"types\" format=\"ascii\">\n");
    for (PetscInt e = 0; e < nt; ++e)
        fprintf(fp, "%d\n", vtkSimplexType[DIM]);
    fprintf(fp, "</DataArray></Cells>\n");

    fprintf(fp, "<PointData Scalars=\"u\">\n");
    fprintf(fp, "<DataArray type=\"Float64\" Name=\"u\" format=\"ascii\">\n");
    for (PetscInt i = 0; i < n; ++i)
        fprintf(fp, "%.17g\n", PetscRealPart(xa[i]));
    fprintf(fp, "</DataArray></PointData>\n");

    fprintf(fp, "</Piece></UnstructuredGrid></VTKFile>\n");
    fclose(fp);

    PetscCall(VecRestoreArrayRead(x, &xa));
    PetscCall(KSPDestroy(&ksp));
    PetscCall(VecDestroy(&x));
    PetscCall(VecDestroy(&rhs));
    PetscFunctionReturn(PETSC_SUCCESS);
}"#

  let code := (code.replace "SOLVER_NAME" name).replace "DIM" (toString dim)
  modify fun s => { s with functions := s.functions ++ [code] }
  return name

private def cStringLiteral (s : String) : String :=
  "\"" ++
    (((s.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" "\\n") ++
  "\""

def ImpExpr.emit {ty : ImpType}
    (e : ImpExpr CRep ty)
    (realLiteral : Realish -> String) :
    StateM EmitState CResult := do

  registerCType ty

  match e with
  | .var x => return { lines := [], value := x }
  | .scalar x =>
      let name <- freshName "v"
      return {
        lines := [s!"double {name} = {realLiteral x};"]
        value := name }
  | .natLit i => return { lines := [], value := toString i.val }
  | .vecOf (l := l) xs =>
      let items <- (List.finRange l).mapM fun i => (xs i).emit realLiteral
      let name <- freshName "v"
      let values := if items.isEmpty then "0" else
        String.intercalate ", " (items.map (fun item => item.value))
      return {
        lines := items.flatMap (fun item => item.lines) ++ [ty.cType ++ " " ++ name ++
          " = { .data = { " ++ values ++ " } };"]
        value := name }
  | .vecLit (l := l) (ty := elem) xs =>
      let name <- freshName "v"
      let t := ImpType.vec l elem
      let assignments := (List.finRange l).map fun i =>
        s!"{name}.data[{i.val}] = {xs i};"
      return {
        lines := [t.cType ++ " " ++ name ++ " = {0};"] ++
                 assignments
        value := name }
  | .mul a b =>
      let x <- a.emit realLiteral
      let y <- b.emit realLiteral
      let name <- freshName "v"
      return {
        lines := x.lines ++ y.lines ++
          [s!"double {name} = {x.value} * {y.value};"]
        value := name }
  | .add a b =>
      let x <- a.emit realLiteral
      let y <- b.emit realLiteral
      let name <- freshName "v"
      return {
        lines := x.lines ++ y.lines ++
          [s!"double {name} = {x.value} + {y.value};"]
        value := name }
  | .matrixAdd state row col value =>
      let i <- row.emit realLiteral
      let j <- col.emit realLiteral
      let v <- value.emit realLiteral
      return {
        lines := i.lines ++ j.lines ++ v.lines ++
          [s!"PetscCall(MatSetValue({state}.matrix, (PetscInt){i.value}, " ++
           s!"(PetscInt){j.value}, {v.value}, ADD_VALUES));"]
        value := state }
  | .loadAdd state row value =>
      let i <- row.emit realLiteral
      let v <- value.emit realLiteral
      return {
        lines := i.lines ++ v.lines ++ [s!"{state}.load[{i.value}] += {v.value};"]
        value := state }
  | .dirichlet state row =>
      let i <- row.emit realLiteral
      let b <- freshName "boundary"
      return {
        lines := i.lines ++
          [s!"PetscInt {b} = (PetscInt){i.value};",
           s!"PetscCall(MatAssemblyBegin({state}.matrix, MAT_FINAL_ASSEMBLY));",
           s!"PetscCall(MatAssemblyEnd({state}.matrix, MAT_FINAL_ASSEMBLY));",
           s!"PetscCall(MatZeroRowsColumns({state}.matrix, 1, &{b}, 1.0, NULL, NULL));",
           s!"{state}.load[{b}] = 0.0;"]
        value := state }
  | .dirichletMany state boundary =>
      let b <- freshName "boundary"
      let i <- freshName "i"
      let values := if boundary.isEmpty then "0" else
        String.intercalate ", " (boundary.map fun v => toString v.val)
      return {
        lines :=
          [s!"static const PetscInt {b}[] = " ++ "{ " ++ values ++ " };",
           s!"PetscCall(MatAssemblyBegin({state}.matrix, MAT_FINAL_ASSEMBLY));",
           s!"PetscCall(MatAssemblyEnd({state}.matrix, MAT_FINAL_ASSEMBLY));",
           s!"PetscCall(MatZeroRowsColumns({state}.matrix, {boundary.length}, " ++
           s!"{b}, 1.0, NULL, NULL));",
           s!"for (size_t {i} = 0; {i} < {boundary.length}; ++{i}) " ++
           "{ " ++ s!"{state}.load[{b}[{i}]] = 0.0;" ++ " }"]
        value := state }
  | .letE rhs body =>
      let x <- rhs.emit realLiteral
      let y <- (body x.value).emit realLiteral
      return {
        lines := x.lines ++ y.lines
        value := y.value }
  | .forL (n := n) (ty := t) init body =>
      let x <- init.emit realLiteral
      let acc <- freshName "acc"
      let i <- freshName "i"
      let y <- (body i acc).emit realLiteral

      let loop :=
        [s!"for (size_t {i} = 0; {i} < {n}; ++{i}) " ++ "{"] ++
        indentLines y.lines ++
        [s!"  {acc} = {y.value};", "}"]

      return {
        lines := x.lines ++
          [s!"{t.cType} {acc} = {x.value};"] ++ loop
        value := acc }
  | .arrAssign arr id value =>
      let i <- id.emit realLiteral
      let v <- value.emit realLiteral
      let name <- freshName "v"
      return {
        lines := i.lines ++ v.lines ++
          [s!"{ty.cType} {name} = {arr};",
           s!"{name}.data[{i.value}] = {v.value};"]
        value := name }
  | .func (dim := dim) (nq := nq) body =>
      let fname <- freshName "kernel"
      let arr <- freshName "arr"
      let detJ <- freshName "detJ"
      let grads <- freshName "grads"

      registerCType (.func dim nq)

      let result <- (body arr detJ grads).emit realLiteral

      let mat := matrixTy dim
      let grad := gradsTy dim nq

      let header :=
        "static " ++ mat.cType ++ " " ++ fname ++
        "(double " ++ detJ ++ ", " ++
        grad.cType ++ " " ++ grads ++ ") {"

      let definition := String.intercalate "\n" <|
        [header,
         "  " ++ mat.cType ++ " " ++ arr ++ " = {0};",
         "  (void)" ++ arr ++ ";",
         "  (void)" ++ grads ++ ";"] ++
        indentLines result.lines ++
        ["  return " ++ result.value ++ ";", "}"]

      modify fun s =>
        { s with functions := s.functions ++ [definition] }

      return { lines := [], value := fname }
  | .app (dim := dim) f detJ grads =>
      let name <- freshName "v"
      let mat := matrixTy dim
      return {
        lines := [
          s!"{mat.cType} {name} = {f}({detJ}, {grads});"
        ]
        value := name }
  | .idx arr id =>
      let a <- arr.emit realLiteral
      let i <- id.emit realLiteral
      let name <- freshName "v"
      return {
        lines := a.lines ++ i.lines ++ [
          s!"{ty.cType} {name} = {a.value}.data[{i.value}];"
        ]
        value := name }
  | @ImpExpr.solve _ dim n nt a b coords elements filename =>
      let solver <- solveFunc dim
      let bb <- freshName "b"
      let cc <- freshName "coords"
      let ee <- freshName "elements"
      let i <- freshName "i"
      let j <- freshName "j"
      return {
        lines := [
          s!"double *{bb} = malloc({n} * sizeof *{bb});",
          s!"double (*{cc})[{dim}] = malloc({n} * sizeof *{cc});",
          s!"PetscInt (*{ee})[{dim + 1}] = malloc({nt} * sizeof *{ee});",

          s!"PetscCheck({bb} && {cc} && {ee}, PETSC_COMM_SELF, PETSC_ERR_MEM, \"Allocation failed\");",

          s!"for (size_t {i} = 0; {i} < {n}; ++{i}) " ++ "{",
          s!"  {bb}[{i}] = {b}.data[{i}];",
          s!"  for (size_t {j} = 0; {j} < {dim}; ++{j}) " ++ "{",
          s!"    {cc}[{i}][{j}] = {coords}.data[{i}].data[{j}];",
          "  }",
          "}",

          s!"for (size_t {i} = 0; {i} < {nt}; ++{i}) " ++ "{",
          s!"  for (size_t {j} = 0; {j} < {dim + 1}; ++{j}) " ++ "{",
          s!"    {ee}[{i}][{j}] = (PetscInt){elements}.data[{i}].data[{j}];",
          "  }",
          "}",

          s!"PetscCall({solver}((PetscInt){n}, {a}, {bb}, (PetscInt){nt}, {cc}, {ee}, {cStringLiteral filename}));",

          s!"free({bb});",
          s!"free({cc});",
          s!"free({ee});"
        ]
        value := "0" }
  | .linearFunc (dim := dim) (nq := nq) body =>
      let fname <- freshName "linear_kernel"
      let arr <- freshName "arr"
      let detJ <- freshName "detJ"
      let grads <- freshName "grads"

      registerCType (.linearFunc dim nq)

      let result <- (body arr detJ grads).emit realLiteral

      let vec := linearTy dim
      let grad := gradsTy dim nq

      let header :=
        "static " ++ vec.cType ++ " " ++ fname ++
        "(double " ++ detJ ++ ", " ++
        grad.cType ++ " " ++ grads ++ ") {"

      let definition := String.intercalate "\n" <|
        [header,
         "  " ++ vec.cType ++ " " ++ arr ++ " = {0};",
         "  (void)" ++ arr ++ ";",
         "  (void)" ++ grads ++ ";"] ++
        indentLines result.lines ++
        ["  return " ++ result.value ++ ";", "}"]

      modify fun s =>
        { s with functions := s.functions ++ [definition] }

      return { lines := [], value := fname }
  | .linearApp (dim := dim) f detJ grads =>
      let name <- freshName "v"
      let vec := linearTy dim
      return {
        lines := [
          s!"{vec.cType} {name} = {f}({detJ}, {grads});"
        ]
        value := name }

def ratToC (x : Rat) : String :=
  s!"({x.num}.0 / {x.den}.0)"

private def renderC (state : EmitState) (lines : List String) : String :=
  String.intercalate "\n" <|
    ["#include <petscksp.h>",
     "#include <stdio.h>",
     "#include <stdlib.h>",
     "#include <stddef.h>"] ++
    state.typedefs ++
    state.functions ++
    ["int main(int argc, char **argv) {",
     "  PetscFunctionBeginUser;",
     "  PetscCall(PetscInitialize(&argc, &argv, NULL, NULL));"] ++
    indentLines lines ++
    ["  PetscCall(PetscFinalize());",
     "  return 0;", "}\n"]

def ImpExpr.emitC {ty : ImpType} (e : ImpExpr CRep ty) : String :=
  let (result, state) := (e.emit ratToC).run {}
  renderC state result.lines

/-- Emit the element loop, sparse scatter-add, and homogeneous Dirichlet elimination. -/
def emitAssembly {dim nq nv nt : Nat}
    (elementCode boundaryCode : ImpExpr CRep (.system nv))
    (coords : Fin nv -> Fin dim -> Realish)
    (elements : Fin nt -> Fin (dim + 1) -> Fin nv)
    (filename : String) : String :=
  let action : StateM EmitState (List String) := do
    let solver <- solveFunc dim
    let element <- elementCode.emit ratToC
    let boundaryResult <- boundaryCode.emit ratToC
    registerCType (gradsTy dim nq)
    let gradTy := (gradsTy dim nq).cType
    let constants := s!"enum " ++ "{ " ++
      s!"dim = {dim}, ndofs = {dim + 1}, nquad = {nq}" ++ " };"
    modify fun s => { s with functions := s.functions ++ [constants] }

    let rows {n width : Nat} (entry : Fin n -> Fin width -> String) : List String :=
      (List.finRange n).map fun i =>
        "  { " ++ String.intercalate ", " ((List.finRange width).map (entry i)) ++ " },"
    let mesh :=
      [s!"const PetscInt n = {nv}, nt = {nt};", "static const double coords[][dim] = {"] ++
      rows (fun i d => ratToC (coords i d)) ++
      ["};", "static const PetscInt elements[][ndofs] = {"] ++
      rows (fun e i => toString (elements e i).val) ++
      ["};"]
    let setup := r#"PetscMPIInt size;
PetscCallMPI(MPI_Comm_size(PETSC_COMM_WORLD, &size));
PetscCheck(size == 1, PETSC_COMM_WORLD, PETSC_ERR_SUP, "Run the solver with one MPI rank");
Mat A;
double *b;
PetscCall(PetscCalloc1(n, &b));
PetscCall(MatCreateSeqAIJ(PETSC_COMM_SELF, n, n, PetscMin(n, 2 * ndofs + 1), NULL, &A));
PetscCall(MatSetOption(A, MAT_NEW_NONZERO_ALLOCATION_ERR, PETSC_FALSE));
T_fem_system system = { .matrix = A, .load = b };
for (PetscInt e = 0; e < nt; ++e) {
    const PetscInt *v = elements[e];
    double detJ, grad[ndofs][dim];"#
    -- TODO: Represent this in Imp_FEM, even though we already prove dx != 0.
    -- Gradients use signed Jacobians. Only the integration measure uses the absolute value.
    let geometry := if dim = 1 then r#"    double dx = coords[v[1]][0] - coords[v[0]][0];
    PetscCheck(dx != 0, PETSC_COMM_SELF, PETSC_ERR_ARG_WRONG, "Degenerate cell %" PetscInt_FMT, e);
    detJ = PetscAbsReal(dx) / 2.0;
    grad[1][0] = 1.0 / dx;
    grad[0][0] = -grad[1][0];"#
      else r#"    double ax = coords[v[1]][0] - coords[v[0]][0];
    double ay = coords[v[1]][1] - coords[v[0]][1];
    double bx = coords[v[2]][0] - coords[v[0]][0];
    double by = coords[v[2]][1] - coords[v[0]][1];
    double det = ax * by - ay * bx;
    PetscCheck(det != 0, PETSC_COMM_SELF, PETSC_ERR_ARG_WRONG, "Degenerate cell %" PetscInt_FMT, e);
    detJ = PetscAbsReal(det);
    grad[1][0] = by / det;
    grad[1][1] = -bx / det;
    grad[2][0] = -ay / det;
    grad[2][1] = ax / det;
    for (size_t d = 0; d < dim; ++d)
        grad[0][d] = -(grad[1][d] + grad[2][d]);"#
    let kernelInputs := r#"    for (size_t q = 0; q < nquad; ++q)
        for (size_t i = 0; i < ndofs; ++i)
            for (size_t d = 0; d < dim; ++d)
                grads.data[q].data[i].data[d] = grad[i][d];"#
    return mesh ++ [setup, geometry, s!"    {gradTy} grads;", kernelInputs] ++
      indentLines element.lines ++ ["}"] ++ boundaryResult.lines ++
      [s!"PetscCall({solver}(n, A, b, nt, coords, elements, {cStringLiteral filename}));",
       "PetscCall(MatDestroy(&A));", "PetscCall(PetscFree(b));"]
  let (lines, state) := action.run {}
  renderC state lines
