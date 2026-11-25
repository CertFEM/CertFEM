/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import Mathlib
import CertFEM.Util
import CertFEM.Quad
import CertFEM.Imp

/-! # IR_QUAD -/

-- IR_QUAD and Imp_FEM are implemented using PHOAS.
-- See the Chlipala paper or this tutorial:
-- https://lean-lang.org/examples/1900-1-1-parametric-higherorder-abstract-syntax/
inductive IrQuadType where
  | real
  | nat (len : Nat)
  | vec (len : Nat) (elem : IrQuadType)
  | func (dim nq : Nat)
  | linearFunc (dim nq : Nat)

@[reducible] def quadTypeToImp : IrQuadType -> ImpType
  | .real => .real
  | .nat n => .nat n
  | .vec n ty => .vec n (quadTypeToImp ty)
  | .func dim nq => .func dim nq
  | .linearFunc dim nq => .linearFunc dim nq

@[reducible] def IrQuadType.denote (ty : IrQuadType) : Type :=
  (quadTypeToImp ty).denote

inductive QuadExpr (rep : IrQuadType -> Type) : IrQuadType -> Type where
  | var {ty : IrQuadType} : rep ty -> QuadExpr rep ty
  | const : Realish -> QuadExpr rep .real
  | natLit {l : Nat} : Fin l -> QuadExpr rep (.nat l)
  | vecLit {l : Nat} {ty : IrQuadType} :
    (Fin l -> QuadExpr rep ty) -> QuadExpr rep (.vec l ty)
  | mul : QuadExpr rep .real -> QuadExpr rep .real -> QuadExpr rep .real
  | summ {l : Nat} :
      (rep (.nat l) -> QuadExpr rep .real) -> QuadExpr rep .real
  | map {l1 l2 : Nat} :
      (rep (.nat l1) -> rep (.nat l2) -> QuadExpr rep .real) ->
      QuadExpr rep (.vec l1 (.vec l2 .real))
  | letE {ty1 ty2 : IrQuadType} :
      QuadExpr rep ty1 ->
      (rep ty1 -> QuadExpr rep ty2) ->
      QuadExpr rep ty2
  | idx {l : Nat} {ty : IrQuadType} :
      QuadExpr rep (.vec l ty) ->
      QuadExpr rep (.nat l) ->
      QuadExpr rep ty
  | map1 {l : Nat} :
      (rep (.nat l) -> QuadExpr rep .real) ->
      QuadExpr rep (.vec l .real)
  | func {dim nq : Nat} :
      (rep .real ->
       rep (.vec nq (.vec (dim + 1) (.vec dim .real))) ->
       QuadExpr rep (.vec (dim + 1) (.vec (dim + 1) .real))) ->
      QuadExpr rep (.func dim nq)
  | linearFunc {dim nq : Nat} :
      (rep .real ->
       rep (.vec nq (.vec (dim + 1) (.vec dim .real))) ->
       QuadExpr rep (.vec (dim + 1) .real)) ->
      QuadExpr rep (.linearFunc dim nq)

def QuadExpr.denote {ty : IrQuadType} (e : QuadExpr IrQuadType.denote ty) : ty.denote :=
  match e with
  | .var v => v
  | .const r => r
  | .natLit i => i
  | .vecLit v => fun i => (v i).denote
  | .mul e1 e2 => e1.denote * e2.denote
  | .summ f =>
      Finset.univ.sum (fun i => (f i).denote)
  | .map f =>
      fun i j => (f i j).denote
  | .letE e1 f =>
      (f e1.denote).denote
  | .idx v k => v.denote (k.denote)
  | .map1 f => fun i => (f i).denote
  | .func f => fun x y => denote (f x y)
  | .linearFunc body =>
      fun detJ grads => QuadExpr.denote (body detJ grads)

abbrev QuadFuncType (nq dim : Nat) : IrQuadType :=
  .func dim nq

abbrev LinearQuadFuncType (nq dim : Nat) : IrQuadType :=
  .linearFunc dim nq

abbrev MatrixKernel (dim nq : Nat) :=
  QuadExpr IrQuadType.denote (QuadFuncType nq dim)

abbrev VectorKernel (dim nq : Nat) :=
  QuadExpr IrQuadType.denote (LinearQuadFuncType nq dim)

/-! ## Quadrature kernel snippets in IR_QUAD -/

def massKernel {dim nq : Nat} {rep : IrQuadType -> Type}
    (q : RatQuadScheme dim nq)
    (basisVals : Fin nq -> Fin (dim + 1) -> Realish)
    : QuadExpr rep (QuadFuncType nq dim) :=
  .func (fun detJ _ =>
  .letE (.vecLit (fun g => .const (q.wts g)))
    (fun weights =>
      .letE (.vecLit (fun g => .vecLit (fun i => .const (basisVals g i))))
        (fun basis =>
          .map (l1 := dim + 1) (l2 := dim + 1)
          (fun i j =>
            .summ (l := nq)
            (fun g =>
              .mul (.var detJ)
                (.mul
                  (.idx (.var weights) (.var g))
                  (.mul
                    (.idx (.idx (.var basis) (.var g)) (.var i))
                    (.idx (.idx (.var basis) (.var g)) (.var j)))))))))

def diffusionKernel {dim nq : Nat} {rep : IrQuadType -> Type}
    (q : RatQuadScheme dim nq)
    (_basisVals : Fin nq -> Fin (dim + 1) -> Realish)
    : QuadExpr rep (QuadFuncType nq dim) :=
  .func (fun detJ grads =>
  .letE (.vecLit (fun g => .const (q.wts g)))
    (fun weights =>
        .map (l1 := dim + 1) (l2 := dim + 1)
          (fun i j =>
            .summ (l := nq)
              (fun g =>
                .mul (.var detJ)
                  (.mul
                    (.idx (.var weights) (.var g))
                    (.summ (l := dim)
                      (fun k =>
                        .mul
                          (.idx (.idx (.idx (.var grads) (.var g)) (.var i)) (.var k))
                          (.idx (.idx (.idx (.var grads) (.var g)) (.var j)) (.var k)))))))))

def advectionKernel {dim nq : Nat} {rep : IrQuadType -> Type}
    (q : RatQuadScheme dim nq)
    (basisVals : Fin nq -> Fin (dim + 1) -> Realish)
    (beta : Fin dim -> Realish)
    : QuadExpr rep (QuadFuncType nq dim) :=
  .func (fun detJ grads =>
  .letE (.vecLit (fun k => .const (beta k))) (fun velocity =>
  .letE (.vecLit (fun g => .const (q.wts g)))
    (fun weights =>
      .letE (.vecLit (fun g => .vecLit (fun i => .const (basisVals g i))))
        (fun basis =>
          .map (l1 := dim + 1) (l2 := dim + 1)
            (fun i j =>
              .summ (l := nq)
                (fun g =>
                  .mul (.var detJ)
                    (.mul
                      (.idx (.var weights) (.var g))
                      (.mul
                        (.idx (.idx (.var basis) (.var g)) (.var i))
                        (.summ (l := dim)
                          (fun k =>
                            .mul
                              (.idx (.var velocity) (.var k))
                              (.idx (.idx (.idx (.var grads) (.var g)) (.var j)) (.var k))))))))))))

def anisotropicDiffusionKernel {dim nq : Nat} {rep : IrQuadType -> Type}
    (q : RatQuadScheme dim nq)
    (_basisVals : Fin nq -> Fin (dim + 1) -> Realish)
    (D : Matrix (Fin dim) (Fin dim) Realish)
    : QuadExpr rep (QuadFuncType nq dim) :=
  .func (fun detJ grads =>
  .letE (.vecLit (fun k => .vecLit (fun l => .const (D k l)))) (fun tensor =>
  .letE (.vecLit (fun g => .const (q.wts g)))
    (fun weights =>
          .map (l1 := dim + 1) (l2 := dim + 1)
            (fun i j =>
              .summ (l := nq)
                (fun g =>
                  .mul (.var detJ)
                    (.mul
                      (.idx (.var weights) (.var g))
                      (.summ (l := dim)
                        (fun k =>
                          .summ (l := dim)
                            (fun l =>
                              .mul
                                (.idx (.idx (.idx (.var grads) (.var g)) (.var i)) (.var k))
                                (.mul
                                  (.idx (.idx (.var tensor) (.var k)) (.var l))
                                  (.idx (.idx (.idx (.var grads) (.var g)) (.var j))
                                    (.var l))))))))))))

def gradientKernel {dim nq : Nat} {rep : IrQuadType -> Type}
    (q : RatQuadScheme dim nq)
    (basisVals : Fin nq -> Fin (dim + 1) -> Realish)
    (dir : Fin dim)
    : QuadExpr rep (QuadFuncType nq dim) :=
  .func (fun detJ grads =>
  .letE (.vecLit (fun g => .const (q.wts g)))
    (fun weights =>
      .letE (.vecLit (fun g => .vecLit (fun i => .const (basisVals g i))))
        (fun basis =>
          .map (l1 := dim + 1) (l2 := dim + 1)
            (fun i j =>
              .summ (l := nq)
                (fun g =>
                  .mul (.var detJ)
                    (.mul
                      (.idx (.var weights) (.var g))
                      (.mul
                        (.idx (.idx (.var basis) (.var g)) (.var i))
                        (.idx (.idx (.idx (.var grads) (.var g)) (.var j)) (.natLit dir)))))))))

def linearKernel {dim nq : Nat} {rep : IrQuadType -> Type}
    (q : RatQuadScheme dim nq)
    (basisVals : Fin nq -> Fin (dim + 1) -> Realish)
    (f : Realish)
    : QuadExpr rep (LinearQuadFuncType nq dim) :=
  .linearFunc (fun detJ _ =>
  .letE (.vecLit (fun g => .const (q.wts g)))
    (fun weights =>
      .letE (.vecLit (fun g => .vecLit (fun i => .const (basisVals g i))))
        (fun basis =>
          .map1 (l := dim + 1)
            (fun i =>
              .summ (l := nq)
                (fun g =>
                  .mul (.var detJ)
                    (.mul
                      (.idx (.var weights) (.var g))
                      (.mul
                        (.const f)
                        (.idx (.idx (.var basis) (.var g)) (.var i)))))))))
