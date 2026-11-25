/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import Mathlib
import CertFEM.Util
import CertFEM.Simplex
import CertFEM.Imp
import CertFEM.Emitter

/-! # Mesh

Functions to create a mesh object, and prove that it does not
contain degenerate cells.
-/

abbrev MkSpace (dim : Nat) := Fin dim -> Realish
abbrev SimplexElement (dim : PNat) :=
  Affine.Simplex Realish (Fin dim -> Realish) dim

def adjacent {dim nv nt : Nat}
    (elements : Fin nt -> Fin (dim + 1) -> Fin nv)
    (e1 e2 : Fin nt) : Prop :=
  e1 != e2 /\
  (Inter.inter
    (Finset.univ.image (elements e1))
    (Finset.univ.image (elements e2))).card = dim

structure Mesh (dim nv nt : Nat) where
  coords : Fin nv -> Fin dim -> Realish
  elements : Fin nt -> Fin (dim + 1) -> Fin nv

def Mesh.elementNondegenerate {dim nv nt : Nat}
    (m : Mesh dim nv nt) (e : Fin nt) : Prop :=
  AffineIndependent Rat
    (fun i => m.coords (m.elements e i))

/-- Equation 5 in Section 6.5 : Mesh Non-degeneracy -/
def Mesh.nondegenerate {dim nv nt : Nat} (m : Mesh dim nv nt) : Prop :=
  forall e : Fin nt,
    AffineIndependent Rat
      (fun i => m.coords (m.elements e i))

/-- Equation 6 (clause 1) in Section 6.6 : Mesh conformity -/
def Mesh.conforming {dim nv nt : Nat} (m : Mesh dim nv nt) : Prop :=
  forall e f : Fin nt,
    Set.inter
      (convexHull Rat (Set.range (fun i => m.coords (m.elements e i))))
      (convexHull Rat (Set.range (fun i => m.coords (m.elements f i)))) =
    convexHull Rat
      (Set.inter
        (Set.range (fun i => m.coords (m.elements e i)))
        (Set.range (fun i => m.coords (m.elements f i))))

/-- Equation 6 (clause 2) in Section 6.6 : Mesh conformity -/
def Mesh.connected {dim nv nt : Nat} (m : Mesh dim nv nt) : Prop :=
  forall e1 e2 : Fin nt,
    Relation.ReflTransGen (adjacent m.elements) e1 e2

private def cVecLiteral (ty : ImpType) (xs : List String) : String :=
  "(" ++ ty.cType ++ "){ .data = { " ++
    String.intercalate ", " xs ++ " } }"

def Mesh.coordsToImp {dim nv nt : Nat}
    (m : Mesh dim nv nt) :
    ImpExpr CRep (.vec nv (.vec dim .real)) :=
  .vecLit (fun v =>
    cVecLiteral (.vec dim .real)
      ((List.finRange dim).map (fun d =>
        ratToC (m.coords v d))))

def Mesh.elemsToImp {dim nv nt : Nat}
    (m : Mesh dim nv nt) :
    ImpExpr CRep (.vec nt (.vec (dim + 1) (.nat nv))) :=
  .vecLit (fun e =>
    cVecLiteral (.vec (dim + 1) (.nat nv))
      ((List.finRange (dim + 1)).map (fun i =>
        toString (m.elements e i).val)))

def Mesh.elemToSimplex {dim nv nt : Nat}
    (m : Mesh dim nv nt)
    (e : Fin nt)
    (h : m.elementNondegenerate e):
    Affine.Simplex Rat (Fin dim -> Rat) dim :=
  { points := fun i => m.coords (m.elements e i)
    independent := h }

def Mesh.toSimplexList {dim nv nt : Nat}
    (m : Mesh dim nv nt)
    (h : m.nondegenerate) :
    List (Affine.Simplex Rat (MkSpace dim) dim) :=
  (List.finRange nt).map (fun e => m.elemToSimplex e (h e))

def Mesh.elementPoints {dim nv nt : Nat} (m : Mesh dim nv nt)
    (e : Fin nt) : Fin (dim + 1) -> MkSpace dim :=
  fun i => m.coords (m.elements e i)

def Mesh.elementVertices {dim nv nt : Nat} (m : Mesh dim nv nt)
    (e : Fin nt) : Finset (Fin nv) :=
  Finset.univ.image (m.elements e)

/-! -/

def unitLineCoords (n : PNat) :
    Fin (n.val + 1) -> MkSpace 1 :=
  fun v _ => (v.val : Rat) / (n.val : Rat)

def unitLineElements (n : PNat) :
    Fin n.val -> Fin 2 -> Fin (n.val + 1) :=
  fun e i =>
    if i = 0 then e.castSucc else e.succ

def unitSquareCoords (n : PNat) :
    Fin ((n.val + 1) * (n.val + 1)) -> MkSpace 2 :=
  fun v =>
    let ij := finProdFinEquiv.symm v
    ![
      (ij.1.val : Rat) / (n.val : Rat),
      (ij.2.val : Rat) / (n.val : Rat)
    ]

/-- Diagonal used to split each square, in Cartesian coordinates. -/
inductive SquareDiagonal where
  | rising
  | falling

def unitSquareElements (n : PNat) (diagonal : SquareDiagonal := .rising) :
    Fin ((n.val * n.val) * 2) ->
    Fin 3 ->
    Fin ((n.val + 1) * (n.val + 1)) :=
  fun e =>
    let ck := finProdFinEquiv.symm e
    let ij := finProdFinEquiv.symm ck.1
    let i := ij.1
    let j := ij.2

    let v00 := finProdFinEquiv (i.castSucc, j.castSucc)
    let v01 := finProdFinEquiv (i.castSucc, j.succ)
    let v11 := finProdFinEquiv (i.succ, j.succ)
    let v10 := finProdFinEquiv (i.succ, j.castSucc)

    match diagonal with
    | .rising => if ck.2 = 0 then ![v00, v11, v10] else ![v00, v01, v11]
    | .falling => if ck.2 = 0 then ![v00, v01, v10] else ![v01, v11, v10]

def unitLineMesh (n : PNat) : Mesh 1 (n + 1) n :=
  { coords := unitLineCoords n
    elements := unitLineElements n }

def unitSquareMesh (n : PNat) (diagonal : SquareDiagonal := .rising) :
    Mesh 2 ((n + 1) * (n + 1)) (2 * n * n) :=
  { coords := unitSquareCoords n
    elements := fun e =>
      unitSquareElements n diagonal (Fin.cast (by ac_rfl) e) }

/-- Boundary vertex indices for the built-in unit interval and unit square meshes. -/
def Mesh.unitBoundary {dim nv nt : Nat} (m : Mesh dim nv nt) : List (Fin nv) :=
  (List.finRange nv).filter fun v =>
    (List.finRange dim).any fun d => m.coords v d == 0 || m.coords v d == 1

noncomputable def Mesh.elementFinset {dim nv nt : Nat}
    (m : Mesh dim nv nt) (e : Fin nt) :
    Finset (MkSpace dim) := by
  classical
  exact Finset.univ.image
    (fun i => m.coords (m.elements e i))

private theorem Mesh.elementFinset_coe {dim nv nt : Nat}
    (m : Mesh dim nv nt) (e : Fin nt) :
    (m.elementFinset e : Set (MkSpace dim)) =
      Set.range (fun i => m.coords (m.elements e i)) := by
  classical
  ext p
  simp [Mesh.elementFinset]

private theorem Mesh.elementFinset_independent {dim nv nt : Nat}
    (m : Mesh dim nv nt)
    (h : m.nondegenerate)
    (e : Fin nt) :
    AffineIndependent Rat
      (fun p : m.elementFinset e => (p : MkSpace dim)) := by
  change AffineIndependent Rat
    (fun p : (m.elementFinset e : Set (MkSpace dim)) =>
      (p : MkSpace dim))
  rw [m.elementFinset_coe e]
  exact (h e).range

private theorem facesGlue
    {E : Type*} [AddCommGroup E] [Module Rat E]
    {A B S T : Finset E}
    (hA : AffineIndependent Rat (fun x : A => (x : E)))
    (hB : AffineIndependent Rat (fun x : B => (x : E)))
    (hS : S <= A)
    (hT : T <= B)
    (hAB :
      Set.inter
        (convexHull Rat (A : Set E))
        (convexHull Rat (B : Set E)) =
      convexHull Rat
        (Set.inter (A : Set E) (B : Set E))) :
    Set.inter
      (convexHull Rat (S : Set E))
      (convexHull Rat (T : Set E)) <=
    convexHull Rat
      (Set.inter (S : Set E) (T : Set E)) := by

  classical
  intro x hx

  have hSA : (S : Set E) <= (A : Set E) := by
    intro p hp
    exact hS hp

  have hTB : (T : Set E) <= (B : Set E) := by
    intro p hp
    exact hT hp

  have hxA : (convexHull Rat (A : Set E)) x :=
    (convexHull_mono hSA) hx.1

  have hxB : (convexHull Rat (B : Set E)) x :=
    (convexHull_mono hTB) hx.2

  have hxI :
      (convexHull Rat
        ((Inter.inter A B : Finset E) : Set E)) x := by
    have h :
        (convexHull Rat
          (Set.inter (A : Set E) (B : Set E))) x := by
      exact Eq.mp
        (congrArg (fun s : Set E => s x) hAB)
        (And.intro hxA hxB)
    simpa only [Finset.coe_inter] using h

  have hxSI :
      (convexHull Rat
        ((Inter.inter S (Inter.inter A B) : Finset E) : Set E)) x := by
    have hsub : Inter.inter A B <= A :=
      Finset.inter_subset_left

    have hHull := hA.convexHull_inter hS hsub

    have h :
        (convexHull Rat
          (Set.inter
            (S : Set E)
            ((Inter.inter A B : Finset E) : Set E))) x := by
      exact (congrArg (fun u : Set E => u x) hHull).symm.mp
        (And.intro hx.1 hxI)

    simpa only [Finset.coe_inter] using h

  have hSIB :
      Inter.inter S (Inter.inter A B) <= B := by
    intro p hp
    exact (Finset.mem_inter.mp (Finset.mem_inter.mp hp).2).2

  have hxSIT :
      (convexHull Rat
        ((Inter.inter (Inter.inter S (Inter.inter A B)) T :
          Finset E) : Set E)) x := by
    have h :
        (convexHull Rat
          (Set.inter
            ((Inter.inter S (Inter.inter A B) : Finset E) : Set E)
            (T : Set E))) x := by
      have hHull := hB.convexHull_inter hSIB hT
      exact (congrArg (fun u : Set E => u x) hHull).symm.mp
        (And.intro hxSI hx.2)
    simpa only [Finset.coe_inter] using h

  have hEq :
      Inter.inter (Inter.inter S (Inter.inter A B)) T =
        Inter.inter S T := by
    ext p
    simp only [Finset.mem_inter]
    constructor
    next =>
      intro hp
      exact And.intro hp.1.1 hp.2
    next =>
      intro hp
      exact And.intro
        (And.intro hp.1 (And.intro (hS hp.1) (hT hp.2)))
        hp.2

  rw [hEq] at hxSIT
  simpa only [Finset.coe_inter] using hxSIT

noncomputable def Mesh.toSimplicialComplex
    {dim nv nt : Nat}
    (m : Mesh dim nv nt)
    (hnd : m.nondegenerate)
    (hconf : m.conforming) :
    Geometry.SimplicialComplex Rat (MkSpace dim) := by

  let faces : Set (Finset (MkSpace dim)) :=
    {s | exists e : Fin nt, s <= m.elementFinset e}

  have hind :
      forall s, faces s ->
        AffineIndependent Rat
          (fun p : s => (p : MkSpace dim)) := by
    intro s hs
    cases hs with
    | intro e he =>
        exact (m.elementFinset_independent hnd e).mono
          (fun p hp => he hp)

  have hdown : IsLowerSet faces := by
    intro a b hba ha
    cases ha with
    | intro e he =>
        exact Exists.intro e (hba.trans he)

  have hfull (e f : Fin nt) :
      Set.inter
        (convexHull Rat (m.elementFinset e : Set (MkSpace dim)))
        (convexHull Rat (m.elementFinset f : Set (MkSpace dim))) =
      convexHull Rat
        (Set.inter
          (m.elementFinset e : Set (MkSpace dim))
          (m.elementFinset f : Set (MkSpace dim))) := by
    simpa only [m.elementFinset_coe e, m.elementFinset_coe f]
      using hconf e f

  have hglue :
      forall s, faces s ->
        forall t, faces t ->
          Set.inter
            (convexHull Rat (s : Set (MkSpace dim)))
            (convexHull Rat (t : Set (MkSpace dim))) <=
          convexHull Rat
            (Set.inter
              (s : Set (MkSpace dim))
              (t : Set (MkSpace dim))) := by
    intro s hs t ht
    cases hs with
    | intro e he =>
        cases ht with
        | intro f hf =>
            exact facesGlue
              (m.elementFinset_independent hnd e)
              (m.elementFinset_independent hnd f)
              he hf (hfull e f)

  exact Geometry.SimplicialComplex.ofErase
    faces hind hdown hglue

/-! # Old code

Old outdated code, please ignore.

## Unit mesh 1D
-/

private def natDivReal (i : Nat) (X : PNat) : Realish :=
  ((i : Rat) / (X : Rat) : Rat)

/-- A point on the 1D Euclidean line. -/
def unitLinePoint (x : Realish) : MkSpace 1 :=
  (fun _ => x)

/-- The two endpoints of cell `i`.

For `X` divisions, cell `i` is: [i / X, (i + 1) / X]
-/
def UnitLineCellPoints {X : PNat} (i : Fin X) : Fin 2 -> MkSpace 1 :=
  ![
    unitLinePoint (natDivReal i.val X),
    unitLinePoint (natDivReal (i.val + 1) X)
  ]

/-- A 1D cell is affine independent if its two endpoints are different.

Generalized version of `line_is_affine_ind`.
-/
lemma unitLineCell_is_affine_ind {X : PNat} (i : Fin X)
    (p0_ne_p1 : Not (UnitLineCellPoints i 0 = UnitLineCellPoints i 1)) :
    AffineIndependent Realish (UnitLineCellPoints i) := by
  simpa [UnitLineCellPoints] using affineIndependent_of_ne Realish p0_ne_p1

/-- Proofs needed to build the unit line mesh.

For every interval cell, its left and right endpoints must be distinct.
-/
structure UnitLineMeshProofs (X : PNat)  where
  endpoint_ne :
    forall i : Fin X,
      Not (UnitLineCellPoints i 0 = UnitLineCellPoints i 1)

/-- One simplex element for cell `i`. -/
def UnitLineCell {X : PNat}
    (h : UnitLineMeshProofs X)
    (i : Fin X) :
    SimplexElement 1 :=
  { points := UnitLineCellPoints i
    independent := unitLineCell_is_affine_ind i (h.endpoint_ne i) }

/-- Unit line mesh from `0` to `1` with `X` divisions.

This returns `X` line elements.
-/
def UnitLineMeshOld (X : PNat)
    (h : UnitLineMeshProofs X) : List (SimplexElement 1) :=
  (List.finRange X).map
    (fun i => UnitLineCell h i)

/-! ## Unit mesh 2D
Functions to construct a unit square mesh.
-/

def unitSquarePoint (x : Realish) (y: Realish) : MkSpace 2 := ![x, y]

/--
For `X` divisions along the first dimension, and `Y` divisions along the second,
cell `i, j` is a tuple of two triangles:
  ([(i / X, j / X), ((i + 1) / X, (j + 1) / Y), ((i + 1) / X, j / X)],
   [(i / X, j / X), (i / X, (j + 1) / Y), ((i + 1) / X, (j + 1) / Y)])
Note that (assuming x increasese to the right, and y increases upwards)
these points on the triangles are listed in clockwise order and the diagnoal is
from bottom-left to top-right corners.
-/
def UnitSquareCellPoints {X : PNat} {Y : PNat}
    (i : Fin X)
    (j : Fin Y) :
    Fin 4 -> MkSpace 2 :=
  ![![natDivReal i.val X, natDivReal j.val Y],
    ![natDivReal i.val X, natDivReal (j.val + 1) Y],
    ![natDivReal (i.val + 1) X, natDivReal (j.val + 1) Y],
    ![natDivReal (i.val + 1) X, natDivReal j.val Y]
  ]

def UnitSquareTrianglePoints {X : PNat} {Y : PNat}
    (i : Fin X)
    (j : Fin Y) :
    Fin 2 -> Fin 3 -> MkSpace 2 :=
  ![
    ![
    UnitSquareCellPoints i j 0,
    UnitSquareCellPoints i j 2,
    UnitSquareCellPoints i j 3
    ],
    ![
    UnitSquareCellPoints i j 0,
    UnitSquareCellPoints i j 1,
    UnitSquareCellPoints i j 2
    ]
  ]

/-- Three points of the plane are not collinear if the determinant of the
matrix formed by the two edge vectors `p 1 - p 0` and `p 2 - p 0` is nonzero.
-/
theorem not_collinear_if_determinant_nonzero (p : Fin 3 -> MkSpace 2)
    (h : Ne ((p 1 0 - p 0 0) * (p 2 1 - p 0 1) -
             (p 1 1 - p 0 1) * (p 2 0 - p 0 0)) 0) :
    Not (Collinear Realish (Set.range p)) := by
  rw [collinear_iff_of_mem (Set.mem_range_self 0)]
  intro hcollinear
  cases hcollinear with
  | intro v hv =>
    cases hv (p 1) (Set.mem_range_self 1) with
    | intro r1 hr1 =>
      cases hv (p 2) (Set.mem_range_self 2) with
      | intro r2 hr2 =>
        apply h
        rw [hr1, hr2]
        simp [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring

/--
The gap between two consecutive grid coordinates is `1 / X`.
-/
theorem natDivReal_succ_sub (i : Nat) (X : PNat) :
    natDivReal (i + 1) X - natDivReal i X = 1 / (X : Real) := by
  unfold natDivReal
  push_cast
  have hX' : Not ((X : Real) = 0) := by positivity
  field_simp
  ring

theorem unitSquareTriangle_is_affine_ind {X : PNat} {Y : PNat}
    (i : Fin X)
    (j : Fin Y)
    (k : Fin 2) :
    AffineIndependent Realish (UnitSquareTrianglePoints i j k) := by

  have step_pos (Z : PNat) (a : Nat) :
      0 < natDivReal (a + 1) Z - natDivReal a Z := by
    apply sub_pos.mpr
    unfold natDivReal
    apply div_lt_div_of_pos_right
    exact_mod_cast Nat.lt_succ_self a
    exact_mod_cast Z.property

  apply affineIndependent_iff_not_collinear.mpr
  apply not_collinear_if_determinant_nonzero
  fin_cases k <;>
    simp only [UnitSquareTrianglePoints, UnitSquareCellPoints,
      Fin.zero_eta, Fin.mk_one, Matrix.cons_val,
      sub_self, mul_zero, zero_mul, zero_sub]

  all_goals
    have hp := mul_pos (step_pos Y j.val) (step_pos X i.val)
    first
    | exact ne_of_gt hp
    | exact neg_ne_zero.mpr (ne_of_gt hp)

def UnitSquareCell {X : PNat} {Y : PNat}
    (i : Fin X)
    (j : Fin Y)
    (k : Fin 2) :
    SimplexElement 2 :=
  { points := UnitSquareTrianglePoints i j k
    independent := unitSquareTriangle_is_affine_ind i j k }

def UnitSquareMesh_structured (X Y : PNat) : List (List (List (SimplexElement 2))) :=
  (List.finRange X).map (fun i =>
    (List.finRange Y).map (fun j =>
      (List.finRange 2).map (fun k => UnitSquareCell i j k)))

def UnitSquareMeshOld (X Y : PNat) : List (SimplexElement 2) :=
  List.flatten (List.flatten (UnitSquareMesh_structured X Y))

/-! ## Mesh obligations used in Sections 6.5-6.6 -/

/-- A mesh satisfying both geometric conformity and face connectivity from the paper.
The computational Mesh structure alone does not contain these proof fields. -/
structure Mesh.Valid {dim nv nt : Nat} (m : Mesh dim nv nt) : Prop where
  nondegenerate : m.nondegenerate
  conforming : m.conforming
  connected : m.connected

/-- Paper "Mesh Non-degeneracy": the edge vectors from the first vertex are independent. -/
theorem Mesh.edgeVectorsIndependent {dim nv nt : Nat} (m : Mesh dim nv nt)
    (h : m.nondegenerate) (e : Fin nt) :
    LinearIndependent Realish (fun i : Fin dim =>
      m.coords (m.elements e i.succ) - m.coords (m.elements e 0)) := by
  have hi := (affineIndependent_iff_linearIndependent_vsub Realish _ 0).mp (h e)
  exact hi.comp (fun i : Fin dim => Subtype.mk i.succ (Fin.succ_ne_zero i))
    (fun i j hij => Fin.succ_injective dim (congrArg Subtype.val hij))

/-- Equation "non-degeneracy" in the paper: nonzero edge weights cannot sum to zero. -/
theorem Mesh.edgeCombination_ne_zero {dim nv nt : Nat} (m : Mesh dim nv nt)
    (h : m.nondegenerate) (e : Fin nt) (w : Fin dim -> Realish) (hw : Ne w 0) :
    Ne (Finset.univ.sum (fun i : Fin dim =>
      fun d => w i * (m.coords (m.elements e i.succ) d - m.coords (m.elements e 0) d))) 0 := by
  intro hz
  apply hw
  have hi := (Fintype.linearIndependent_iff.mp (m.edgeVectorsIndependent h e)) w
  apply funext
  exact hi (by simpa only [Pi.smul_def, smul_eq_mul, Pi.sub_apply] using hz)
