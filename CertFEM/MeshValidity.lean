/-
SPDX-License-Identifier: AGPL-3.0-only
SPDX-FileCopyrightText: Copyright 2025-2026 <ANONYMIZED>
-/

import CertFEM.Mesh

/-! # Validity of the generated unit meshes (Sections 6.5-6.6). -/

/-- Paper "Mesh Non-degeneracy": every generated unit-line cell has distinct endpoints. -/
theorem unitLineMesh_nondegenerate (n : PNat) : (unitLineMesh n).nondegenerate := by
  intro e
  have hp : (0 : Realish) < n.val := by exact_mod_cast n.property
  have he : Ne (unitLineCoords n e.castSucc) (unitLineCoords n e.succ) := by
    intro h
    have h0 := congrFun h 0
    have hlt : (e.val : Realish) / n.val < ((e.val + 1 : Nat) : Realish) / n.val :=
      div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self e.val) hp
    exact (ne_of_lt hlt) h0
  have hpoints : (fun i => (unitLineMesh n).coords ((unitLineMesh n).elements e i)) =
      ![unitLineCoords n e.castSucc, unitLineCoords n e.succ] := by
    funext i
    fin_cases i <;> rfl
  rw [hpoints]
  exact affineIndependent_of_ne Realish he

/-- Paper "Mesh Non-degeneracy": both choices of unit-square diagonal yield nonzero-area cells. -/
theorem unitSquareMesh_nondegenerate (n : PNat) (diagonal : SquareDiagonal) :
    (unitSquareMesh n diagonal).nondegenerate := by
  intro e
  apply affineIndependent_iff_not_collinear.mpr
  apply not_collinear_if_determinant_nonzero
  have hp : (0 : Realish) < n.val := by exact_mod_cast n.property
  let ijk := finProdFinEquiv.symm (Fin.cast (by ac_rfl) e : Fin ((n.val * n.val) * 2))
  let ij := finProdFinEquiv.symm ijk.1
  have hi : ((ij.1.val + 1 : Nat) : Realish) / n.val - (ij.1.val : Realish) / n.val > 0 :=
    sub_pos.mpr (div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self ij.1.val) hp)
  have hj : ((ij.2.val + 1 : Nat) : Realish) / n.val - (ij.2.val : Realish) / n.val > 0 :=
    sub_pos.mpr (div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self ij.2.val) hp)
  generalize hk : ijk.2 = k
  cases diagonal <;> fin_cases k <;>
    simp only [unitSquareMesh, unitSquareElements, unitSquareCoords,
      show finProdFinEquiv.symm (Fin.cast (by ac_rfl) e : Fin ((n.val * n.val) * 2)) = ijk
        from rfl, hk, Equiv.symm_apply_apply, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceEq, if_true, if_false, Fin.val_castSucc, Fin.val_succ] <;>
    dsimp only [ij] at hi hj <;> nlinarith [mul_pos hi hj]

private theorem hull_glue_of_separator {d m k : Nat}
    (p : Fin m -> MkSpace d) (q : Fin k -> MkSpace d)
    (L : LinearMap (RingHom.id Realish) (MkSpace d) Realish) (c : Realish)
    (hp : forall a, L (p a) <= c) (hq : forall b, c <= L (q b))
    (hface : forall a, L (p a) = c -> Membership.mem (Set.range q) (p a)) :
    Set.inter (convexHull Realish (Set.range p)) (convexHull Realish (Set.range q)) =
      convexHull Realish (Set.inter (Set.range p) (Set.range q)) := by
  classical
  apply Set.Subset.antisymm
  . intro x hx
    have hxle : L x <= c := convexHull_min (by
      intro y hy
      cases hy with
      | intro a ha => simpa only [<- ha] using hp a)
      ((convex_Iic c).linear_preimage L) hx.1
    have hxge : c <= L x := convexHull_min (by
      intro y hy
      cases hy with
      | intro b hb => simpa only [<- hb] using hq b)
      ((convex_Ici c).linear_preimage L) hx.2
    have heq : L x = c := le_antisymm hxle hxge
    let vertices : Finset (MkSpace d) := Finset.univ.image p
    have hv : (vertices : Set (MkSpace d)) = Set.range p := by
      ext y
      simp [vertices]
    have hxv : Membership.mem (convexHull Realish (vertices : Set (MkSpace d))) x := by
      rw [hv]
      exact hx.1
    cases Finset.mem_convexHull'.mp hxv with
    | intro w hw =>
      have hw0 := hw.1
      have hw1 := hw.2.1
      have hwx := hw.2.2
      have hLp (y : MkSpace d) (hy : Membership.mem vertices y) : L y <= c := by
        have hyr : Membership.mem (Set.range p) y := by rw [<- hv]; exact hy
        cases hyr with
        | intro a ha => simpa only [<- ha] using hp a
      have hgap : vertices.sum (fun y => w y * (c - L y)) = 0 := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, <- Finset.sum_mul, hw1, one_mul]
        have hsum : vertices.sum (fun y => w y * L y) = L x := by
          rw [<- hwx, map_sum]
          simp only [map_smul, smul_eq_mul]
        rw [hsum, heq, sub_self]
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun y hy =>
        mul_nonneg (hw0 y hy) (sub_nonneg.mpr (hLp y hy)))).mp hgap
      let support : Finset (MkSpace d) := vertices.filter (fun y => Ne (w y) 0)
      have hs : support <= vertices := Finset.filter_subset _ _
      have hwout (y : MkSpace d) (hy : Membership.mem vertices y)
          (hout : Not (Membership.mem support y)) : w y = 0 := by
        simpa only [support, Finset.mem_filter, hy, true_and, not_not] using hout
      have hws : support.sum w = 1 := by
        rw [Finset.sum_subset hs hwout]
        exact hw1
      have hxs : support.sum (fun y => HSMul.hSMul (w y) y) = x := by
        rw [Finset.sum_subset hs (fun y hy hout => by rw [hwout y hy hout, zero_smul])]
        exact hwx
      rw [<- hxs]
      apply (convex_convexHull Realish _).sum_mem (fun y hy => hw0 y (hs hy)) hws
      intro y hy
      have hyv := hs hy
      have hwne : Ne (w y) 0 := (Finset.mem_filter.mp hy).2
      have hplane : L y = c := by
        have hprod := hzero y hyv
        have hz := (mul_eq_zero.mp hprod).resolve_left hwne
        exact (sub_eq_zero.mp hz).symm
      apply subset_convexHull
      have hyr : Membership.mem (Set.range p) y := by rw [<- hv]; exact hyv
      refine And.intro hyr ?_
      cases hyr with
      | intro a ha =>
          subst y
          exact hface a hplane
  . exact Set.subset_inter (convexHull_mono Set.inter_subset_left)
      (convexHull_mono Set.inter_subset_right)

private def coordLinear {d : Nat} (a : Fin d) :
    LinearMap (RingHom.id Realish) (MkSpace d) Realish where
  toFun x := x a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Paper "Mesh Conformity": generated unit-line cells intersect only in shared faces. -/
theorem unitLineMesh_conforming (n : PNat) : (unitLineMesh n).conforming := by
  have hp : (0 : Realish) < n.val := by exact_mod_cast n.property
  have glue (e f : Fin n.val) (h : e < f) :
      Set.inter
        (convexHull Realish (Set.range (fun a => unitLineCoords n (unitLineElements n e a))))
        (convexHull Realish (Set.range (fun a => unitLineCoords n (unitLineElements n f a)))) =
      convexHull Realish (Set.inter
        (Set.range (fun a => unitLineCoords n (unitLineElements n e a)))
        (Set.range (fun a => unitLineCoords n (unitLineElements n f a)))) := by
    apply hull_glue_of_separator _ _ (coordLinear 0) ((f.val : Realish) / n.val)
    . intro a
      change (unitLineCoords n (unitLineElements n e a)) 0 <= _
      fin_cases a <;> simp [unitLineElements, unitLineCoords]
      all_goals apply div_le_div_of_nonneg_right _ hp.le
      all_goals norm_cast
      all_goals exact le_of_lt h
    . intro b
      change _ <= (unitLineCoords n (unitLineElements n f b)) 0
      fin_cases b <;> simp [unitLineElements, unitLineCoords]
      all_goals apply div_le_div_of_nonneg_right _ hp.le
      all_goals norm_cast
      all_goals omega
    . intro a ha
      refine Exists.intro (0 : Fin 2) ?_
      apply funext
      intro d
      fin_cases d
      exact ha.symm
  intro e f
  rcases lt_trichotomy e f with h | h | h
  . exact glue e f h
  . subst f
    have hi (s : Set (MkSpace 1)) : Set.inter s s = s := Set.ext fun _ => and_self_iff
    rw [hi, hi]
  . have hi (s t : Set (MkSpace 1)) : Set.inter s t = Set.inter t s :=
      Set.ext fun _ => and_comm
    rw [hi, hi (Set.range _) (Set.range _)]
    exact glue f e h

private theorem finiteChainConnected {n : Nat} (R : Fin n -> Fin n -> Prop)
    (hR : Symmetric R)
    (hstep : forall (a : Fin n) (h : a.val + 1 < n), R a (Fin.mk (a.val + 1) h)) :
    forall a b, Relation.ReflTransGen R a b := by
  intro a b
  have hn : 0 < n := Nat.zero_lt_of_lt a.isLt
  have hfrom : forall (k : Nat) (hk : k < n),
      Relation.ReflTransGen R (Fin.mk 0 hn) (Fin.mk k hk) := by
    intro k
    induction k with
    | zero => intro hk; exact .refl
    | succ k ih =>
        intro hk
        exact (ih (by omega)).tail (hstep (Fin.mk k (by omega)) hk)
  exact (Relation.ReflTransGen.symmetric hR (hfrom a.val a.isLt)).trans (hfrom b.val b.isLt)

private theorem unitLineElementVertices (n : PNat) (e : Fin n.val) :
    Finset.univ.image (unitLineElements n e) = {e.castSucc, e.succ} := by
  ext v
  simp [Fin.exists_fin_succ, unitLineElements, eq_comm]

/-- Paper "Mesh Conformity", connectivity clause: consecutive unit-line cells share one endpoint. -/
theorem unitLineMesh_connected (n : PNat) : (unitLineMesh n).connected := by
  apply finiteChainConnected
  . intro e f h
    change adjacent (unitLineElements n) e f at h
    change adjacent (unitLineElements n) f e
    simp only [adjacent, bne_iff_ne] at *
    exact And.intro (Ne.symm h.1) (by simpa only [Finset.inter_comm] using h.2)
  . intro a h
    let b : Fin n.val := Fin.mk (a.val + 1) h
    change adjacent (unitLineElements n) a b
    constructor
    . simp only [b, bne_iff_ne, ne_eq, Fin.ext_iff]
      omega
    . rw [unitLineElementVertices, unitLineElementVertices]
      have hab : a.succ = b.castSucc := Fin.ext rfl
      have h0 : Ne a.castSucc b.castSucc := by intro h; have := congrArg Fin.val h; simp [b] at *
      have h1 : Ne a.castSucc b.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp [b] at hv
        omega
      have h2 : Ne a.succ b.succ := by intro h; have := congrArg Fin.val h; simp [b] at *
      have hinter : Inter.inter ({a.castSucc, a.succ} : Finset (Fin (n.val + 1)))
          {b.castSucc, b.succ} = {a.succ} := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        grind
      rw [hinter]
      exact Finset.card_singleton _

/-- The current unit-line generator satisfies every mesh obligation in Sections 6.5-6.6. -/
theorem unitLineMesh_valid (n : PNat) : (unitLineMesh n).Valid :=
  { nondegenerate := unitLineMesh_nondegenerate n
    conforming := unitLineMesh_conforming n
    connected := unitLineMesh_connected n }

private def GridGlue {d m k : Nat} (p : Fin m -> MkSpace d) (q : Fin k -> MkSpace d) : Prop :=
  Set.inter (convexHull Realish (Set.range p)) (convexHull Realish (Set.range q)) =
    convexHull Realish (Set.inter (Set.range p) (Set.range q))

private theorem gridGlue_refl {d m : Nat} (p : Fin m -> MkSpace d) : GridGlue p p := by
  have hi (s : Set (MkSpace d)) : Set.inter s s = s := Set.ext fun _ => and_self_iff
  unfold GridGlue
  rw [hi, hi]

private theorem gridGlue_symm {d m k : Nat} {p : Fin m -> MkSpace d} {q : Fin k -> MkSpace d}
    (h : GridGlue p q) : GridGlue q p := by
  have hi (s t : Set (MkSpace d)) : Set.inter s t = Set.inter t s :=
    Set.ext fun _ => and_comm
  unfold GridGlue at *
  rw [hi, hi (Set.range q) (Set.range p)]
  exact h

private theorem gridGlue_image {d m k : Nat} (p : Fin m -> MkSpace d) (q : Fin k -> MkSpace d)
    (F : AffineMap Realish (MkSpace d) (MkSpace d)) (hF : Function.Injective F)
    (h : GridGlue p q) : GridGlue (fun a => F (p a)) (fun b => F (q b)) := by
  have himage (r : Set (MkSpace d)) (t : Set (MkSpace d)) :
      Set.inter (F '' r) (F '' t) = F '' Set.inter r t := (Set.image_inter hF).symm
  have hrange {j : Nat} (r : Fin j -> MkSpace d) :
      Set.range (fun a => F (r a)) = F '' Set.range r := (Set.range_comp F r)
  unfold GridGlue at *
  rw [hrange, hrange, <- F.image_convexHull, <- F.image_convexHull, himage, h,
    F.image_convexHull, himage]

private def gridTriangle (diagonal : SquareDiagonal) (i j : Realish) (k : Fin 2) :
    Fin 3 -> MkSpace 2 :=
  match diagonal with
  | .rising => if k = 0 then ![![i, j], ![i + 1, j + 1], ![i + 1, j]]
      else ![![i, j], ![i, j + 1], ![i + 1, j + 1]]
  | .falling => if k = 0 then ![![i, j], ![i, j + 1], ![i + 1, j]]
      else ![![i, j + 1], ![i + 1, j + 1], ![i + 1, j]]

private def planeLinear (a b : Realish) :
    LinearMap (RingHom.id Realish) (MkSpace 2) Realish where
  toFun x := a * x 0 + b * x 1
  map_add' x y := by simp; ring
  map_smul' c x := by simp [Pi.smul_apply, smul_eq_mul]; ring

-- Each neighboring-cell case has a small rational separating-plane certificate.
-- `decide` checks the certificates in Lean's kernel; no native evaluation is used.
private theorem gridTriangle_near_glue (diagonal : SquareDiagonal)
    (dx dy : Fin 3) (k l : Fin 2) :
    GridGlue (gridTriangle diagonal 0 0 k)
      (gridTriangle diagonal ((dx.val : Realish) - 1) ((dy.val : Realish) - 1) l) := by
  cases diagonal with
  | rising =>
    fin_cases dx <;> fin_cases dy <;> fin_cases k <;> fin_cases l
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (0)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (0)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (-1)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (-1)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (0)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (1)) ((1/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (0)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (1)) ((1/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (1)) ((3/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (-1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (-1)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (-1)) ((1/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (-1)) (0) <;> decide +kernel
    . norm_num only [Nat.cast_ofNat, sub_self]
      exact gridGlue_refl _
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (1)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (-1)) (0) <;> decide +kernel
    . norm_num only [Nat.cast_ofNat, sub_self]
      exact gridGlue_refl _
    . apply hull_glue_of_separator _ _ (planeLinear (0) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (1)) ((1/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (-1)) ((3/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (-1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (-1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (-1)) ((1/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (-1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (0)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (-1)) ((1/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (0)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (0)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (0)) (1) <;> decide +kernel
  | falling =>
    fin_cases dx <;> fin_cases dy <;> fin_cases k <;> fin_cases l
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (-1)) ((1/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (-1)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (-1)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (-1)) ((-1/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (-1)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (0)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (-1)) ((-1/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (0)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (0)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (0)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (-1)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (-1)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (-1)) ((-1/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (-1)) (0) <;> decide +kernel
    . norm_num only [Nat.cast_ofNat, sub_self]
      exact gridGlue_refl _
    . apply hull_glue_of_separator _ _ (planeLinear (1) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (-1) (-1)) (-1) <;> decide +kernel
    . norm_num only [Nat.cast_ofNat, sub_self]
      exact gridGlue_refl _
    . apply hull_glue_of_separator _ _ (planeLinear (0) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (1)) ((3/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (1)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (1)) (2) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (0)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (0)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (-1)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (0) (-1)) (0) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (0)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (1)) ((3/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (0)) (1) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (1)) (2) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (1)) ((3/2)) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (1)) (2) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (1)) (2) <;> decide +kernel
    . apply hull_glue_of_separator _ _ (planeLinear (1) (1)) ((5/2)) <;> decide +kernel

private def translateGrid (i j : Realish) : AffineMap Realish (MkSpace 2) (MkSpace 2) :=
  (LinearMap.id : Module.End Realish (MkSpace 2)).toAffineMap +
    AffineMap.const Realish (MkSpace 2) ![i, j]

private theorem translateGrid_injective (i j : Realish) :
    Function.Injective (translateGrid i j) := by
  intro x y h
  funext d
  have hd := congrFun h d
  simpa [translateGrid] using hd

private theorem gridTriangle_shift (diagonal : SquareDiagonal) (x y i j : Realish) (k : Fin 2) :
    (fun a => translateGrid x y (gridTriangle diagonal i j k a)) =
      gridTriangle diagonal (x + i) (y + j) k := by
  funext a d
  cases diagonal <;> fin_cases k <;> fin_cases a <;> fin_cases d <;>
    simp [gridTriangle, translateGrid] <;> ring

private theorem gridTriangle_bounds (diagonal : SquareDiagonal) (i j : Realish) (k : Fin 2)
    (a : Fin 3) :
    i <= gridTriangle diagonal i j k a 0 /\ gridTriangle diagonal i j k a 0 <= i + 1 /\
    j <= gridTriangle diagonal i j k a 1 /\ gridTriangle diagonal i j k a 1 <= j + 1 := by
  cases diagonal <;> fin_cases k <;> fin_cases a <;> simp [gridTriangle]

private theorem gridTriangle_farX (diagonal : SquareDiagonal) (i j x y : Realish) (k l : Fin 2)
    (h : i + 1 < x) : GridGlue (gridTriangle diagonal i j k) (gridTriangle diagonal x y l) := by
  apply hull_glue_of_separator _ _ (coordLinear 0) ((i + 1 + x) / 2)
  . intro a
    have hb := (gridTriangle_bounds diagonal i j k a).2.1
    change gridTriangle diagonal i j k a 0 <= _
    linarith
  . intro b
    have hb := (gridTriangle_bounds diagonal x y l b).1
    change _ <= gridTriangle diagonal x y l b 0
    linarith
  . intro a ha
    have hb := (gridTriangle_bounds diagonal i j k a).2.1
    change gridTriangle diagonal i j k a 0 = _ at ha
    exfalso
    linarith

private theorem gridTriangle_farY (diagonal : SquareDiagonal) (i j x y : Realish) (k l : Fin 2)
    (h : j + 1 < y) : GridGlue (gridTriangle diagonal i j k) (gridTriangle diagonal x y l) := by
  apply hull_glue_of_separator _ _ (coordLinear 1) ((j + 1 + y) / 2)
  . intro a
    have hb := (gridTriangle_bounds diagonal i j k a).2.2.2
    change gridTriangle diagonal i j k a 1 <= _
    linarith
  . intro b
    have hb := (gridTriangle_bounds diagonal x y l b).2.2.1
    change _ <= gridTriangle diagonal x y l b 1
    linarith
  . intro a ha
    have hb := (gridTriangle_bounds diagonal i j k a).2.2.2
    change gridTriangle diagonal i j k a 1 = _ at ha
    exfalso
    linarith

private theorem gridTriangle_glue (diagonal : SquareDiagonal) (i j x y : Int) (k l : Fin 2) :
    GridGlue (gridTriangle diagonal i j k) (gridTriangle diagonal x y l) := by
  by_cases hx : i + 1 < x
  . exact gridTriangle_farX diagonal i j x y k l (by exact_mod_cast hx)
  by_cases hx' : x + 1 < i
  . exact gridGlue_symm (gridTriangle_farX diagonal x y i j l k (by exact_mod_cast hx'))
  by_cases hy : j + 1 < y
  . exact gridTriangle_farY diagonal i j x y k l (by exact_mod_cast hy)
  by_cases hy' : y + 1 < j
  . exact gridGlue_symm (gridTriangle_farY diagonal x y i j l k (by exact_mod_cast hy'))
  have hdx : 0 <= x - i + 1 /\ x - i + 1 < 3 := by omega
  have hdy : 0 <= y - j + 1 /\ y - j + 1 < 3 := by omega
  let dx : Fin 3 := Fin.mk (x - i + 1).toNat (by omega)
  let dy : Fin 3 := Fin.mk (y - j + 1).toNat (by omega)
  have hxval : (dx.val : Realish) - 1 = (x : Realish) - i := by
    dsimp [dx]
    exact_mod_cast (show ((x - i + 1).toNat : Int) - 1 = x - i by omega)
  have hyval : (dy.val : Realish) - 1 = (y : Realish) - j := by
    dsimp [dy]
    exact_mod_cast (show ((y - j + 1).toNat : Int) - 1 = y - j by omega)
  have hnear := gridTriangle_near_glue diagonal dx dy k l
  rw [hxval, hyval] at hnear
  have himage := gridGlue_image _ _ (translateGrid i j) (translateGrid_injective i j) hnear
  simpa only [gridTriangle_shift, add_zero, add_sub_cancel] using himage

private theorem coordsPair (n : PNat) (a b : Fin (n.val + 1)) :
    unitSquareCoords n (finProdFinEquiv (a, b)) =
      ![(a.val : Realish) / n.val, (b.val : Realish) / n.val] := by
  simp only [unitSquareCoords, Equiv.symm_apply_apply]

private theorem unitSquare_cell_points (n : PNat) (diagonal : SquareDiagonal)
    (i j : Fin n.val) (k : Fin 2) :
    (fun a => unitSquareCoords n (unitSquareElements n diagonal
      (finProdFinEquiv (finProdFinEquiv (i, j), k)) a)) =
      (fun a => AffineMap.homothety (0 : MkSpace 2) (1 / (n.val : Realish))
        (gridTriangle diagonal i.val j.val k a)) := by
  funext a
  simp only [unitSquareElements, Equiv.symm_apply_apply]
  cases diagonal <;> fin_cases k <;> fin_cases a <;>
    simp only [gridTriangle, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one,
      Fin.reduceEq, if_true, if_false]
  all_goals
    rw [coordsPair]
    funext d
    fin_cases d <;>
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_fin_one, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one,
        AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, sub_zero, add_zero,
        Pi.smul_apply, smul_eq_mul] <;> ring

private theorem unitSquareMesh_points (n : PNat) (diagonal : SquareDiagonal)
    (e : Fin (2 * n.val * n.val)) :
    (fun a => (unitSquareMesh n diagonal).coords ((unitSquareMesh n diagonal).elements e a)) =
      (let cell := finProdFinEquiv.symm
          (Fin.cast (by ac_rfl) e : Fin ((n.val * n.val) * 2))
       let ij := finProdFinEquiv.symm cell.1
       fun a => AffineMap.homothety (0 : MkSpace 2) (1 / (n.val : Realish))
         (gridTriangle diagonal ij.1.val ij.2.val cell.2 a)) := by
  let cell := finProdFinEquiv.symm
    (Fin.cast (by ac_rfl) e : Fin ((n.val * n.val) * 2))
  let ij := finProdFinEquiv.symm cell.1
  have hinner : finProdFinEquiv (ij.1, ij.2) = cell.1 := finProdFinEquiv.apply_symm_apply _
  have houter : finProdFinEquiv (finProdFinEquiv (ij.1, ij.2), cell.2) =
      (Fin.cast (by ac_rfl) e : Fin ((n.val * n.val) * 2)) := by
    rw [hinner]
    exact finProdFinEquiv.apply_symm_apply _
  exact (congrArg (fun idx => fun a => unitSquareCoords n
    (unitSquareElements n diagonal idx a)) houter).symm.trans
    (unitSquare_cell_points n diagonal ij.1 ij.2 cell.2)

/-- Paper "Mesh Conformity": for either diagonal, generated square triangles meet
exactly along the convex hull of their common vertices. -/
theorem unitSquareMesh_conforming (n : PNat) (diagonal : SquareDiagonal) :
    (unitSquareMesh n diagonal).conforming := by
  intro e f
  change GridGlue
    (fun a => (unitSquareMesh n diagonal).coords ((unitSquareMesh n diagonal).elements e a))
    (fun a => (unitSquareMesh n diagonal).coords ((unitSquareMesh n diagonal).elements f a))
  rw [unitSquareMesh_points, unitSquareMesh_points]
  let ec := finProdFinEquiv.symm (Fin.cast (by ac_rfl) e : Fin ((n.val * n.val) * 2))
  let fc := finProdFinEquiv.symm (Fin.cast (by ac_rfl) f : Fin ((n.val * n.val) * 2))
  let ei := finProdFinEquiv.symm ec.1
  let fi := finProdFinEquiv.symm fc.1
  have hgrid : GridGlue (gridTriangle diagonal ei.1.val ei.2.val ec.2)
      (gridTriangle diagonal fi.1.val fi.2.val fc.2) := by
    simpa only [Int.cast_natCast] using gridTriangle_glue diagonal
      (ei.1.val : Int) (ei.2.val : Int) (fi.1.val : Int) (fi.2.val : Int) ec.2 fc.2
  have hn : Ne (n.val : Realish) 0 := by exact_mod_cast (Nat.ne_of_gt n.property)
  exact gridGlue_image _ _ (AffineMap.homothety (0 : MkSpace 2) (1 / (n.val : Realish)))
    (AffineMap.homothety_injective _ (one_div_ne_zero hn)) hgrid

private theorem unitSquareCoords_injective (n : PNat) :
    Function.Injective (unitSquareCoords n) := by
  intro a b h
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  . apply Fin.ext
    have hx := congrFun h 0
    simp only [unitSquareCoords, Matrix.cons_val_zero] at hx
    have hn : Ne (n.val : Realish) 0 := by exact_mod_cast (Nat.ne_of_gt n.property)
    exact_mod_cast (div_left_inj' hn).mp hx
  . apply Fin.ext
    have hy := congrFun h 1
    simp only [unitSquareCoords, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hy
    have hn : Ne (n.val : Realish) 0 := by exact_mod_cast (Nat.ne_of_gt n.property)
    exact_mod_cast (div_left_inj' hn).mp hy

private abbrev PointEdge {A : Type} [DecidableEq A] (p q : Fin 3 -> A) : Prop :=
  (Inter.inter (Finset.univ.image p) (Finset.univ.image q)).card = 2

private theorem pointEdge_image {A B : Type} [DecidableEq A] [DecidableEq B]
    (p q : Fin 3 -> A) (F : A -> B) (hi : Function.Injective F) (h : PointEdge p q) :
    PointEdge (fun a => F (p a)) (fun a => F (q a)) := by
  unfold PointEdge at *
  have heq : Inter.inter (Finset.univ.image (fun a => F (p a)))
      (Finset.univ.image (fun a => F (q a))) =
        (Inter.inter (Finset.univ.image p) (Finset.univ.image q)).image F := by
    rw [Finset.image_inter _ _ hi]
    simp only [Finset.image_image, Function.comp_def]
  rw [heq, Finset.card_image_of_injective _ hi, h]

private theorem gridTriangle_edge_same (diagonal : SquareDiagonal) :
    PointEdge (gridTriangle diagonal 0 0 0) (gridTriangle diagonal 0 0 1) := by
  cases diagonal <;> decide +kernel

private theorem gridTriangle_edge_y (diagonal : SquareDiagonal) :
    PointEdge (gridTriangle diagonal 0 0 1) (gridTriangle diagonal 0 1 0) := by
  cases diagonal <;> decide +kernel

private def xSide (diagonal : SquareDiagonal) : Fin 2 :=
  match diagonal with | .rising => 0 | .falling => 1

private theorem gridTriangle_edge_x (diagonal : SquareDiagonal) :
    PointEdge (gridTriangle diagonal 0 0 (xSide diagonal))
      (gridTriangle diagonal 1 0 (1 - xSide diagonal)) := by
  cases diagonal <;> decide +kernel

private def squareIndex (n : PNat) (i j : Fin n.val) (k : Fin 2) : Fin (2 * n.val * n.val) :=
  Fin.cast (by ac_rfl) (finProdFinEquiv (finProdFinEquiv (i, j), k))

private theorem squareIndex_points (n : PNat) (diagonal : SquareDiagonal)
    (i j : Fin n.val) (k : Fin 2) :
    (fun a => (unitSquareMesh n diagonal).coords
      ((unitSquareMesh n diagonal).elements (squareIndex n i j k) a)) =
      (fun a => AffineMap.homothety (0 : MkSpace 2) (1 / (n.val : Realish))
        (gridTriangle diagonal i.val j.val k a)) := by
  rw [unitSquareMesh_points]
  simp [squareIndex]

private theorem square_adjacent_of_pointEdge (n : PNat) (diagonal : SquareDiagonal)
    (e f : Fin (2 * n.val * n.val))
    (h : PointEdge
      (fun a => (unitSquareMesh n diagonal).coords ((unitSquareMesh n diagonal).elements e a))
      (fun a => (unitSquareMesh n diagonal).coords ((unitSquareMesh n diagonal).elements f a))) :
    adjacent (unitSquareMesh n diagonal).elements e f := by
  constructor
  . simp only [bne_iff_ne]
    intro hef
    subst f
    unfold PointEdge at h
    rw [Finset.inter_self, Finset.card_image_of_injective _
      ((unitSquareMesh_nondegenerate n diagonal e).injective)] at h
    norm_num at h
  . have hc : Function.Injective (unitSquareMesh n diagonal).coords :=
      unitSquareCoords_injective n
    have hi := Finset.image_inter
      (Finset.univ.image ((unitSquareMesh n diagonal).elements e))
      (Finset.univ.image ((unitSquareMesh n diagonal).elements f)) hc
    unfold PointEdge at h
    rw [<- Finset.card_image_of_injective _ hc, hi]
    simpa only [Finset.image_image, Function.comp_def] using h

private theorem square_adjacent_grid (n : PNat) (diagonal : SquareDiagonal)
    (i j x y : Fin n.val) (k l : Fin 2)
    (h : PointEdge (gridTriangle diagonal i.val j.val k)
      (gridTriangle diagonal x.val y.val l)) :
    adjacent (unitSquareMesh n diagonal).elements (squareIndex n i j k) (squareIndex n x y l) := by
  apply square_adjacent_of_pointEdge
  rw [squareIndex_points, squareIndex_points]
  have hn : Ne (n.val : Realish) 0 := by exact_mod_cast (Nat.ne_of_gt n.property)
  exact pointEdge_image _ _ (AffineMap.homothety (0 : MkSpace 2) (1 / (n.val : Realish)))
    (AffineMap.homothety_injective _ (one_div_ne_zero hn)) h

private theorem square_adjacent_same (n : PNat) (diagonal : SquareDiagonal) (i j : Fin n.val) :
    adjacent (unitSquareMesh n diagonal).elements (squareIndex n i j 0) (squareIndex n i j 1) := by
  apply square_adjacent_grid
  have h := pointEdge_image _ _ (translateGrid i.val j.val)
    (translateGrid_injective i.val j.val) (gridTriangle_edge_same diagonal)
  simpa only [gridTriangle_shift, add_zero] using h

private theorem square_adjacent_y (n : PNat) (diagonal : SquareDiagonal)
    (i j : Fin n.val) (hj : j.val + 1 < n.val) :
    adjacent (unitSquareMesh n diagonal).elements (squareIndex n i j 1)
      (squareIndex n i (Fin.mk (j.val + 1) hj) 0) := by
  apply square_adjacent_grid
  have h := pointEdge_image _ _ (translateGrid i.val j.val)
    (translateGrid_injective i.val j.val) (gridTriangle_edge_y diagonal)
  simpa only [gridTriangle_shift, add_zero, Nat.cast_add, Nat.cast_one] using h

private theorem square_adjacent_x (n : PNat) (diagonal : SquareDiagonal)
    (i j : Fin n.val) (hi : i.val + 1 < n.val) :
    adjacent (unitSquareMesh n diagonal).elements (squareIndex n i j (xSide diagonal))
      (squareIndex n (Fin.mk (i.val + 1) hi) j (1 - xSide diagonal)) := by
  apply square_adjacent_grid
  have h := pointEdge_image _ _ (translateGrid i.val j.val)
    (translateGrid_injective i.val j.val) (gridTriangle_edge_x diagonal)
  simpa only [gridTriangle_shift, add_zero, Nat.cast_add, Nat.cast_one] using h

private theorem adjacent_symmetric {dim nv nt : Nat}
    (elements : Fin nt -> Fin (dim + 1) -> Fin nv) : Symmetric (adjacent elements) := by
  intro e f h
  simp only [adjacent, bne_iff_ne] at *
  exact And.intro (Ne.symm h.1) (by simpa only [Finset.inter_comm] using h.2)

private theorem finiteChainPaths {n : Nat} {A : Type} (R : A -> A -> Prop) (hR : Symmetric R)
    (f : Fin n -> A) (hstep : forall (a : Fin n) (h : a.val + 1 < n),
      Relation.ReflTransGen R (f a) (f (Fin.mk (a.val + 1) h))) :
    forall a b, Relation.ReflTransGen R (f a) (f b) := by
  intro a b
  have hn : 0 < n := Nat.zero_lt_of_lt a.isLt
  have hfrom : forall (k : Nat) (hk : k < n),
      Relation.ReflTransGen R (f (Fin.mk 0 hn)) (f (Fin.mk k hk)) := by
    intro k
    induction k with
    | zero => intro hk; exact .refl
    | succ k ih => intro hk; exact (ih (by omega)).trans (hstep (Fin.mk k (by omega)) hk)
  exact (Relation.ReflTransGen.symmetric hR (hfrom a.val a.isLt)).trans (hfrom b.val b.isLt)

private theorem square_sameCell_path (n : PNat) (diagonal : SquareDiagonal) (i j : Fin n.val)
    (k l : Fin 2) : Relation.ReflTransGen (adjacent (unitSquareMesh n diagonal).elements)
      (squareIndex n i j k) (squareIndex n i j l) := by
  fin_cases k <;> fin_cases l
  . exact .refl
  . exact .single (square_adjacent_same n diagonal i j)
  . exact .single (adjacent_symmetric _ (square_adjacent_same n diagonal i j))
  . exact .refl

private theorem square_y_path (n : PNat) (diagonal : SquareDiagonal) (i j y : Fin n.val) :
    Relation.ReflTransGen (adjacent (unitSquareMesh n diagonal).elements)
      (squareIndex n i j 0) (squareIndex n i y 0) := by
  apply finiteChainPaths _ (adjacent_symmetric _) (fun j => squareIndex n i j 0) _ j y
  intro a ha
  exact (square_sameCell_path n diagonal i a 0 1).tail (square_adjacent_y n diagonal i a ha)

private theorem square_x_path (n : PNat) (diagonal : SquareDiagonal) (j i x : Fin n.val) :
    Relation.ReflTransGen (adjacent (unitSquareMesh n diagonal).elements)
      (squareIndex n i j 0) (squareIndex n x j 0) := by
  apply finiteChainPaths _ (adjacent_symmetric _) (fun i => squareIndex n i j 0) _ i x
  intro a ha
  exact ((square_sameCell_path n diagonal a j 0 (xSide diagonal)).tail
    (square_adjacent_x n diagonal a j ha)).trans
    (square_sameCell_path n diagonal (Fin.mk (a.val + 1) ha) j (1 - xSide diagonal) 0)

/-- Paper "Mesh Conformity", connectivity clause: any two generated square triangles
are connected through complete shared edges, for either diagonal choice. -/
theorem unitSquareMesh_connected (n : PNat) (diagonal : SquareDiagonal) :
    (unitSquareMesh n diagonal).connected := by
  intro e f
  let ec := finProdFinEquiv.symm (Fin.cast (by ac_rfl) e : Fin ((n.val * n.val) * 2))
  let fc := finProdFinEquiv.symm (Fin.cast (by ac_rfl) f : Fin ((n.val * n.val) * 2))
  let ei := finProdFinEquiv.symm ec.1
  let fi := finProdFinEquiv.symm fc.1
  have he : squareIndex n ei.1 ei.2 ec.2 = e := by
    have hinner : finProdFinEquiv (ei.1, ei.2) = ec.1 := finProdFinEquiv.apply_symm_apply _
    have houter : finProdFinEquiv (ec.1, ec.2) =
        (Fin.cast (by ac_rfl) e : Fin ((n.val * n.val) * 2)) := finProdFinEquiv.apply_symm_apply _
    apply Fin.ext
    change (finProdFinEquiv (finProdFinEquiv (ei.1, ei.2), ec.2)).val = e.val
    rw [hinner]
    exact congrArg Fin.val houter
  have hf : squareIndex n fi.1 fi.2 fc.2 = f := by
    have hinner : finProdFinEquiv (fi.1, fi.2) = fc.1 := finProdFinEquiv.apply_symm_apply _
    have houter : finProdFinEquiv (fc.1, fc.2) =
        (Fin.cast (by ac_rfl) f : Fin ((n.val * n.val) * 2)) := finProdFinEquiv.apply_symm_apply _
    apply Fin.ext
    change (finProdFinEquiv (finProdFinEquiv (fi.1, fi.2), fc.2)).val = f.val
    rw [hinner]
    exact congrArg Fin.val houter
  rw [<- he, <- hf]
  let z : Fin n.val := Fin.mk 0 n.property
  exact (square_sameCell_path n diagonal ei.1 ei.2 ec.2 0).trans
    ((square_y_path n diagonal ei.1 ei.2 z).trans
      ((square_x_path n diagonal z ei.1 fi.1).trans
        ((square_y_path n diagonal fi.1 z fi.2).trans
          (square_sameCell_path n diagonal fi.1 fi.2 0 fc.2))))

/-- The current unit-square generator satisfies every mesh obligation in Sections 6.5-6.6. -/
theorem unitSquareMesh_valid (n : PNat) (diagonal : SquareDiagonal) :
    (unitSquareMesh n diagonal).Valid :=
  { nondegenerate := unitSquareMesh_nondegenerate n diagonal
    conforming := unitSquareMesh_conforming n diagonal
    connected := unitSquareMesh_connected n diagonal }
