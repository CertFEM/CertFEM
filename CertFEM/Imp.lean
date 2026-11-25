/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import Mathlib
import CertFEM.Util

/-! Imp_FEM -/

inductive ImpType where
  | unit
  | real
  | nat (len : Nat)
  | vec (len : Nat) (elem : ImpType)
  | func (dim : Nat) (nq : Nat)
  | linearFunc (dim nq : Nat)
  | system (n : Nat)

@[reducible] def ImpType.denote : ImpType -> Type
  | .unit => Unit
  | .real => Realish
  | .nat l => Fin l
  | .vec l v => Fin l -> v.denote
  | .func dim nq =>
      Realish ->
      (Fin nq -> Fin (dim + 1) -> Fin dim -> Realish)
      -> (Fin (dim + 1) -> Fin (dim + 1) -> Realish)
  | .linearFunc dim nq =>
      Realish ->
      (Fin nq -> Fin (dim + 1) -> Fin dim -> Realish) ->
      (Fin (dim + 1) -> Realish)
  | .system n => Prod (Fin n -> Fin n -> Realish) (Fin n -> Realish)

inductive ImpExpr (rep : ImpType -> Type) : ImpType -> Type where
  | var {ty : ImpType} : rep ty -> ImpExpr rep ty
  | scalar : Realish -> ImpExpr rep .real
  | natLit {l : Nat} : Fin l -> ImpExpr rep (.nat l)
  | vecOf {l : Nat} {ty : ImpType} :
    (Fin l -> ImpExpr rep ty) -> ImpExpr rep (.vec l ty)
  | vecLit {l : Nat} {ty : ImpType} :
    (Fin l -> (rep ty)) -> ImpExpr rep (.vec l ty)
  | mul : ImpExpr rep .real -> ImpExpr rep .real -> ImpExpr rep .real
  | add : ImpExpr rep .real -> ImpExpr rep .real -> ImpExpr rep .real
  | matrixAdd {n : Nat} :
      rep (.system n) -> ImpExpr rep (.nat n) -> ImpExpr rep (.nat n) ->
      ImpExpr rep .real -> ImpExpr rep (.system n)
  | loadAdd {n : Nat} :
      rep (.system n) -> ImpExpr rep (.nat n) -> ImpExpr rep .real ->
      ImpExpr rep (.system n)
  | dirichlet {n : Nat} :
      rep (.system n) -> ImpExpr rep (.nat n) -> ImpExpr rep (.system n)
  | dirichletMany {n : Nat} :
      rep (.system n) -> List (Fin n) -> ImpExpr rep (.system n)
  | letE {a b : ImpType} : -- technically variable assignment, but whatever
      ImpExpr rep a ->
      (rep a -> ImpExpr rep b) ->
      ImpExpr rep b
  | forL {n : Nat} {ty : ImpType} :
      ImpExpr rep ty ->
      (rep (.nat n) -> rep ty -> ImpExpr rep ty) ->
      ImpExpr rep ty
  | arrAssign {l : Nat} {ty : ImpType} :
    rep (.vec l ty) ->
    ImpExpr rep (.nat l) ->
    ImpExpr rep ty ->
    ImpExpr rep (.vec l ty)
  | app {dim nq : Nat} :
      rep (.func dim nq) ->
      rep .real ->
      rep (.vec nq (.vec (dim + 1) (.vec dim .real))) ->
      ImpExpr rep (.vec (dim + 1) (.vec (dim + 1) .real))
  | idx {l : Nat} {ty : ImpType} :
      ImpExpr rep (.vec l ty) ->
      ImpExpr rep (.nat l) ->
      ImpExpr rep ty
  | solve {dim n nt : Nat} :
      rep (.vec n (.vec n .real)) ->
      rep (.vec n .real) ->
      rep (.vec n (.vec dim .real)) ->
      rep (.vec nt (.vec (dim + 1) (.nat n))) ->
      String ->
      ImpExpr rep .unit
  | linearApp {dim nq : Nat} :
      rep (.linearFunc dim nq) ->
      rep .real ->
      rep (.vec nq (.vec (dim + 1) (.vec dim .real))) ->
      ImpExpr rep (.vec (dim + 1) .real)
  | func {dim nq : Nat} :
      (rep (.vec (dim + 1) (.vec (dim + 1) .real)) ->
       rep .real ->
       rep (.vec nq (.vec (dim + 1) (.vec dim .real))) ->
       ImpExpr rep (.vec (dim + 1) (.vec (dim + 1) .real))) ->
      ImpExpr rep (.func dim nq)
  | linearFunc {dim nq : Nat} :
      (rep (.vec (dim + 1) .real) ->
       rep .real ->
       rep (.vec nq (.vec (dim + 1) (.vec dim .real))) ->
       ImpExpr rep (.vec (dim + 1) .real)) ->
      ImpExpr rep (.linearFunc dim nq)

def ImpExpr.denote {ty : ImpType} (e : ImpExpr ImpType.denote ty) : ty.denote :=
  match e with
  | var x =>
      x
  | scalar x =>
      x
  | natLit i => i
  | vecOf xs => fun i => (xs i).denote
  | vecLit xs =>
      xs
  | mul x y =>
      x.denote * y.denote
  | add x y =>
      x.denote + y.denote
  | matrixAdd s i j v =>
      (Function.update s.1 i.denote
        (Function.update (s.1 i.denote) j.denote (s.1 i.denote j.denote + v.denote)), s.2)
  | loadAdd s i v =>
      (s.1, Function.update s.2 i.denote (s.2 i.denote + v.denote))
  | dirichlet s b =>
      (fun i j => if i = b.denote then (if j = b.denote then 1 else 0)
        else if j = b.denote then 0 else s.1 i j,
       Function.update s.2 b.denote 0)
  | dirichletMany s bs =>
      bs.foldl (fun state b =>
        (fun i j => if i = b then (if j = b then 1 else 0)
          else if j = b then 0 else state.1 i j,
         Function.update state.2 b 0)) s
  | letE e body =>
      (body e.denote).denote
  | forL (n := n) init body =>
      (List.finRange n).foldl
        (fun acc i => (body i acc).denote)
        init.denote
  | arrAssign arr i val =>
      Function.update arr i.denote val.denote
  | idx arr i =>
      arr.denote i.denote
  | solve _ _ _ _ _ =>
      ()
  | .func body =>
      fun detJ grads =>
        ImpExpr.denote (body (fun _ _ => 0) detJ grads)
  | .linearFunc body =>
      fun detJ grads =>
        ImpExpr.denote (body (fun _ => 0) detJ grads)
  | .app f detJ grads =>
      f detJ grads
  | .linearApp f detJ grads =>
      f detJ grads

/-- Exact matrix/load state used by sparse assembly semantics. -/
abbrev FEMSystem (n : Nat) := (ImpType.system n).denote
