import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier

namespace Cartier

variable {X : Scheme.{0}}

def secOnOf {L : LB X} (t : L.Sec) (V : X.Opens) : ∀ i, Γ(X, V ⊓ L.U i) :=
  fun i => resG X inf_le_right (t.f i)

theorem secOnOf_mem {L : LB X} (t : L.Sec) (V : X.Opens) : secOnOf t V ∈ secOn L V := fun i j =>
  (resG_resG _ _ _).trans ((sec_compat t i j (inf_le_left.trans inf_le_right) inf_le_right).trans
    (congrArg _ (resG_resG _ _ _).symm))

theorem bijOn_secOnOf_top (L : LB X) :
    Set.BijOn (fun t : L.Sec => secOnOf t ⊤) Set.univ (secOn L ⊤) := by
  have le : ∀ i, L.U i ≤ ⊤ ⊓ L.U i := fun i => le_inf le_top le_rfl
  refine ⟨fun t _ => secOnOf_mem t ⊤, fun t _ t' _ e => sec_ext fun i => ?_, fun t ht => ?_⟩
  · have := congrArg (resG X (le i)) (congrFun e i)
    simp only [secOnOf, resG_resG, resG_self] at this
    exact this
  · refine ⟨⟨fun i => resG X (le i) (t i), fun i j => ?_⟩, trivial, funext fun i =>
      (resG_resG _ _ _).trans (resG_self _ _)⟩
    have := congrArg (resG X (inf_le_inf_right _ (le i) : L.U i ⊓ L.U j ≤ ⊤ ⊓ L.U i ⊓ L.U j))
      (ht i j)
    rw [map_mul, resG_resG, resG_resG, resG_resG, resG_self] at this
    exact (resG_resG _ _ _).trans (this.trans (congrArg _ (resG_resG _ _ _).symm))

instance nonempty_top [IsIntegral X] : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

theorem ratOf_secOnOf_self [IsIntegral X] {L : LB X} (hL : L.IsLB) {s : L.Sec}
    (hs : IsRegularSec s) (V : X.Opens) [Nonempty V] : ratOf hL s V (secOnOf s V) = 1 := by
  have hm : genericPoint X ∈ V ⊓ L.U (genericChart hL) :=
    ⟨genericPoint_mem V, mem_genericChart hL⟩
  have hne : @id X.functionField
      ((X.presheaf.germ _ _ (mem_genericChart hL)).hom (s.f (genericChart hL))) ≠ 0 :=
    nonZeroDivisors.ne_zero (isRegularFn_iff_germ.1 (hs _) _ _)
  have key : ∀ a b : X.functionField, a = b → b ≠ 0 → a * b⁻¹ = 1 := fun a b e hb => by
    rw [e, mul_inv_cancel₀ hb]
  exact key _ _ (germ_resG inf_le_right _ hm _) hne

end Cartier

structure EffCartierData (X : Scheme.{0}) where

  ι : Type

  U : ι → X.Opens

  f : ∀ i, Γ(X, U i)

  cover : ⨆ i, U i = ⊤

  regular : ∀ i, IsRegularFn (f i)

  assoc : ∀ i j, Associated (resG X (inf_le_left : U i ⊓ U j ≤ U i) (f i))
    (resG X (inf_le_right : U i ⊓ U j ≤ U j) (f j))

namespace EffCartierData

variable {X Y Z : Scheme.{0}}

def principal (a : Γ(X, ⊤)) (ha : IsRegularFn a) : EffCartierData X where
  ι := PUnit
  U _ := ⊤
  f _ := a
  cover := iSup_const
  regular _ := ha
  assoc _ _ := Associated.refl _

theorem isRegularFn_spec {R : Type} [CommRing R] {r : R} (hr : r ∈ nonZeroDivisors R) :
    IsRegularFn (X := Sp R) (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
  refine (isRegularFn_iff_of_isAffineOpen (isAffineOpen_top _)).2 ?_
  refine mem_nonZeroDivisors_iff_right.2 fun t ht => ?_
  have e := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ht
  rw [map_mul, map_zero, Iso.inv_hom_id_apply] at e
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (mem_nonZeroDivisors_iff_right.1 hr _ e)
  rwa [Iso.hom_inv_id_apply, map_zero] at this

def ofElement {R : Type} [CommRing R] (r : R) (hr : r ∈ nonZeroDivisors R) :
    EffCartierData (Sp R) :=
  principal _ (isRegularFn_spec hr)

def lineOrigin : EffCartierData (Sp (Polynomial ℤ)) :=
  ofElement Polynomial.X (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero)

def principalTwist (a : Γ(X, ⊤)) (ha : IsRegularFn a) (u : Γ(X, ⊤)ˣ) : EffCartierData X where
  ι := Bool
  U _ := ⊤
  f b := cond b (u * a) a
  cover := iSup_const
  regular b := by
    cases b
    exacts [ha, (IsRegularFn.of_isUnit u.isUnit).mul ha]
  assoc b c := by
    refine Associated.map _ ?_
    cases b <;> cases c
    exacts [Associated.refl _, associated_unit_mul_right _ _ u.isUnit,
      associated_unit_mul_left _ _ u.isUnit, Associated.refl _]

def zero (X : Scheme.{0}) : EffCartierData X := principal 1 (IsRegularFn.of_isUnit isUnit_one)

variable (D D' : EffCartierData X)

theorem exists_mem (x : X) : ∃ i, x ∈ D.U i :=
  Opens.mem_iSup.1 (D.cover.ge (Set.mem_univ x))

def trans (i j : D.ι) : Γ(X, D.U i ⊓ D.U j)ˣ := (D.assoc i j).symm.choose

theorem trans_spec (i j : D.ι) :
    resG X (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (D.f i) =
      (D.trans i j : Γ(X, D.U i ⊓ D.U j)) * resG X (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (D.f j) :=
  ((mul_comm _ _).trans (D.assoc i j).symm.choose_spec).symm

theorem trans_spec_on (i j : D.ι) {W : X.Opens} (hi : W ≤ D.U i) (hj : W ≤ D.U j) :
    resG X hi (D.f i) =
      resG X (le_inf hi hj) (D.trans i j : Γ(X, D.U i ⊓ D.U j)) * resG X hj (D.f j) := by
  have := congrArg (resG X (le_inf hi hj)) (D.trans_spec i j)
  rwa [map_mul, resG_resG, resG_resG] at this

theorem eq_trans_on (i j : D.ι) {W : X.Opens} (hi : W ≤ D.U i) (hj : W ≤ D.U j) {c : Γ(X, W)}
    (hc : resG X hi (D.f i) = c * resG X hj (D.f j)) :
    c = resG X (le_inf hi hj) (D.trans i j : Γ(X, D.U i ⊓ D.U j)) :=
  ((D.regular j).resG hj).mul_right_cancel (hc.symm.trans (D.trans_spec_on i j hi hj))

theorem eq_trans (i j : D.ι) {u : Γ(X, D.U i ⊓ D.U j)ˣ}
    (hu : resG X (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (D.f i) =
      (u : Γ(X, D.U i ⊓ D.U j)) * resG X (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (D.f j)) :
    u = D.trans i j :=
  Units.ext (((D.regular j).resG _).mul_right_cancel (hu.symm.trans (D.trans_spec i j)))

def lb : LB X where
  ι := D.ι
  U := D.U
  g := D.trans

theorem isLB_lb : D.lb.IsLB where
  cover := D.cover
  g_self i := Units.ext (D.eq_trans_on i i le_rfl le_rfl (c := 1) (one_mul _).symm).symm
  cocycle i j k := by
    have hi : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i := inf_le_left.trans inf_le_left
    have hj : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j := inf_le_left.trans inf_le_right
    have hk : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U k := inf_le_right
    refine Units.ext (D.eq_trans_on i k hi hk ?_)
    rw [D.trans_spec_on i j hi hj, D.trans_spec_on j k hj hk, ← mul_assoc]
    rfl

def canonical : D.lb.Sec where
  f := D.f
  compat := D.trans_spec

@[simp] theorem canonical_f (i : D.ι) : D.canonical.f i = D.f i := rfl

theorem isRegularSec_canonical : IsRegularSec D.canonical := D.regular

theorem associated_germ (i j : D.ι) (x : X) (hi : x ∈ D.U i) (hj : x ∈ D.U j) :
    Associated ((X.presheaf.germ _ x hi).hom (D.f i)) ((X.presheaf.germ _ x hj).hom (D.f j)) := by
  have hm : x ∈ D.U i ⊓ D.U j := ⟨hi, hj⟩
  have := (D.assoc i j).map (X.presheaf.germ _ x hm).hom
  rwa [germ_resG, germ_resG] at this

section LocIdeal

variable {κ : Type} (V : κ → X.Opens) (g : ∀ c, Γ(X, V c)) (hV : ∀ x : X, ∃ c, x ∈ V c)
  (hg : ∀ c c' (x : X) (hx : x ∈ V c) (hx' : x ∈ V c'),
    Associated ((X.presheaf.germ _ x hx).hom (g c)) ((X.presheaf.germ _ x hx').hom (g c')))

include hg in

theorem exists_unit_germ (c c' : κ) (x : X) (hx : x ∈ V c) (hx' : x ∈ V c') :
    ∃ u : (X.presheaf.stalk x)ˣ,
      X.presheaf.germ (V c) x hx (g c) = u * X.presheaf.germ (V c') x hx' (g c') := by
  obtain ⟨u, hu⟩ := (hg c c' x hx hx').symm
  exact ⟨u, hu.symm.trans (mul_comm _ _)⟩

def locIdeal : X.IdealSheafData where
  ideal := dsJ V g
  map_ideal_basicOpen := dsJ_basicOpen hV (exists_unit_germ V g hg)

theorem mem_locIdeal_iff {W : X.affineOpens} {a : Γ(X, W.1)} :
    a ∈ (locIdeal V g hV hg).ideal W ↔ ∀ c x (hx : x ∈ W.1) (hc : x ∈ V c),
      (X.presheaf.germ _ x hc).hom (g c) ∣ (X.presheaf.germ _ x hx).hom a := by
  refine mem_dsJ.trans ⟨fun h c x hx hc => ?_, fun h x hx => ?_⟩
  · have := h x hx
    rw [dsK_eq (exists_unit_germ V g hg) c hc] at this
    exact Ideal.mem_span_singleton.1 this
  · obtain ⟨c, hc⟩ := hV x
    rw [dsK_eq (exists_unit_germ V g hg) c hc]
    exact Ideal.mem_span_singleton.2 (h c x hx hc)

theorem ideal_locIdeal (W : X.affineOpens) (c : κ) (h : W.1 ≤ V c) :
    (locIdeal V g hV hg).ideal W = Ideal.span {resG X h (g c)} := by
  ext a
  rw [mem_locIdeal_iff, W.2.mem_ideal_iff]
  refine ⟨fun H x hx => ?_, fun H c' x hx hc' => ?_⟩
  · rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, germ_resG]
    exact H c x hx (h hx)
  · have := H x hx
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, germ_resG] at this
    exact (hg c' c x hc' (h hx)).dvd.trans this

end LocIdeal

def idealSheaf : X.IdealSheafData := locIdeal D.U D.f D.exists_mem D.associated_germ

theorem ideal_idealSheaf (W : X.affineOpens) (i : D.ι) (h : W.1 ≤ D.U i) :
    D.idealSheaf.ideal W = Ideal.span {resG X h (D.f i)} :=
  ideal_locIdeal _ _ _ _ W i h

theorem mem_idealSheaf_iff {W : X.affineOpens} {a : Γ(X, W.1)} :
    a ∈ D.idealSheaf.ideal W ↔ ∀ i, resG X (inf_le_right : W.1 ⊓ D.U i ≤ D.U i) (D.f i) ∣
      resG X (inf_le_left : W.1 ⊓ D.U i ≤ W.1) a := by
  refine (mem_locIdeal_iff _ _ _ _).trans ⟨fun h i => ?_, fun h i x hx hi => ?_⟩
  · refine ((D.regular i).resG _).dvd_of_germ fun x hx => ?_
    rw [germ_resG, germ_resG]
    exact h i x hx.1 hx.2
  · have hm : x ∈ W.1 ⊓ D.U i := ⟨hx, hi⟩
    have := map_dvd (X.presheaf.germ _ x hm).hom (h i)
    rwa [germ_resG, germ_resG] at this

theorem exists_affine_le {V : X.Opens} {x : X} (hx : x ∈ V) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ W.1 ≤ V := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact ⟨⟨W, hW⟩, hxW, hWV⟩

theorem stalkId_idealSheaf (i : D.ι) (x : X) (hx : x ∈ D.U i) :
    FinalTheorems.stalkId D.idealSheaf x = Ideal.span {(X.presheaf.germ _ x hx).hom (D.f i)} := by
  obtain ⟨W, hxW, hW⟩ := exists_affine_le hx
  rw [ds_stalkId_eq_map _ W x hxW, D.ideal_idealSheaf W i hW, Ideal.map_span, Set.image_singleton,
    germ_resG]

theorem eq_idealSheaf {I : X.IdealSheafData}
    (h : ∀ x : X, ∃ (W : X.affineOpens) (i : D.ι) (hW : W.1 ≤ D.U i),
      x ∈ W.1 ∧ I.ideal W = Ideal.span {resG X hW (D.f i)}) : I = D.idealSheaf := by
  choose W i hW hx hI using h
  exact Scheme.IdealSheafData.ext_of_iSup_eq_top W
    (eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩)
    fun x => (hI x).trans (D.ideal_idealSheaf _ _ _).symm

theorem effCartier_idealSheaf : FinalTheorems.EffCartier D.idealSheaf := fun x => by
  obtain ⟨i, hi⟩ := D.exists_mem x
  obtain ⟨W, hxW, hW⟩ := exists_affine_le hi
  exact ⟨W, _, hxW, D.regular i _ hW, D.ideal_idealSheaf W i hW⟩

abbrev zeroScheme : Scheme.{0} := D.idealSheaf.subscheme

abbrev zeroSchemeι : D.zeroScheme ⟶ X := D.idealSheaf.subschemeι

theorem mem_support_iff (i : D.ι) {x : X} (hx : x ∈ D.U i) :
    x ∈ D.idealSheaf.support ↔ x ∉ X.basicOpen (D.f i) := by
  refine (mem_support_iff_stalkId D.idealSheaf x).trans ?_
  rw [D.stalkId_idealSheaf i x hx, Ne, Ideal.span_singleton_eq_top, X.mem_basicOpen _ x hx]

theorem coe_nonzeroLocus_canonical :
    (Out.nonzeroLocus D.canonical : Set X) = (D.idealSheaf.support : Set X)ᶜ := by
  ext x
  obtain ⟨i, hi⟩ := D.exists_mem x
  exact (mem_nonzeroLocus_iff D.canonical i hi).trans
    (not_not.symm.trans (not_congr (D.mem_support_iff i hi)).symm)

theorem coe_nonzeroLocus_canonical_eq_compl_range :
    (Out.nonzeroLocus D.canonical : Set X) = (Set.range D.zeroSchemeι)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, coe_nonzeroLocus_canonical]

theorem dense_nonzeroLocus_canonical : Dense (Out.nonzeroLocus D.canonical : Set X) := by
  refine dense_iff_inter_open.2 fun V hV ⟨x, hx⟩ => ?_
  obtain ⟨i, hi⟩ := D.exists_mem x
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := ⟨V, hV⟩ ⊓ D.U i) ⟨hx, hi⟩
  have hWi : W.1 ≤ D.U i := hW.trans inf_le_right
  by_contra hne
  have hbot : X.basicOpen (resG X hWi (D.f i)) = ⊥ := by
    refine eq_bot_iff.2 fun y hy => hne ⟨y, (hW (X.basicOpen_le _ hy)).1, ?_⟩
    have hyW : y ∈ W.1 := X.basicOpen_le _ hy
    refine (mem_nonzeroLocus_iff D.canonical i (hWi hyW)).2 ?_
    rw [X.mem_basicOpen _ y hyW] at hy
    exact (X.mem_basicOpen _ y (hWi hyW)).2 ((congrArg IsUnit (germ_resG hWi y hyW _)).mp hy)
  obtain ⟨n, hn⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact W.2.isCompact _).2 hbot
  have : Nonempty W.1 := ⟨⟨x, hxW⟩⟩
  exact (((D.regular i).resG hWi).pow n).ne_zero hn

theorem associated_of_idealSheaf_eq (h : D.idealSheaf = D'.idealSheaf) (p : D'.ι) (q : D.ι) :
    Associated (resG X (inf_le_right : D'.U p ⊓ D.U q ≤ D.U q) (D.f q))
      (resG X (inf_le_left : D'.U p ⊓ D.U q ≤ D'.U p) (D'.f p)) :=
  ((D.regular q).resG _).associated_of_germ ((D'.regular p).resG _) fun x hx => by
    rw [germ_resG, germ_resG, ← stalkId_idealSheaf, ← stalkId_idealSheaf, h]

theorem existsUnique_iso_of_idealSheaf_eq (h : D.idealSheaf = D'.idealSheaf) :
    ∃! w : LB.Iso D.lb D'.lb, w.IsGen ∧ SecMaps w D.canonical D'.canonical :=
  existsUnique_secMaps D.regular (D.associated_of_idealSheaf_eq D' h)

theorem lbIso_of_idealSheaf_eq (h : D.idealSheaf = D'.idealSheaf) : LBIso D.lb D'.lb :=
  (D.existsUnique_iso_of_idealSheaf_eq D' h).exists.imp fun _ hw => hw.1

theorem idealSheaf_eq_of_secMaps {w : LB.Iso D.lb D'.lb}
    (hw : SecMaps w D.canonical D'.canonical) : D.idealSheaf = D'.idealSheaf := by
  refine D'.eq_idealSheaf fun x => ?_
  obtain ⟨q, hq⟩ := D.exists_mem x
  obtain ⟨p, hp⟩ := D'.exists_mem x
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := D'.U p ⊓ D.U q) ⟨hp, hq⟩
  refine ⟨W, p, hW.trans inf_le_left, hxW, ?_⟩
  rw [D.ideal_idealSheaf W q (hW.trans inf_le_right)]
  exact (Ideal.span_singleton_mul_left_unit ((Units.isUnit _).map _) _).symm.trans
    (congrArg (fun a => Ideal.span {a})
      (hw.on p q (hW.trans inf_le_left) (hW.trans inf_le_right)).symm)

theorem idealSheaf_eq_iff : D.idealSheaf = D'.idealSheaf ↔
    ∃ w : LB.Iso D.lb D'.lb, w.IsGen ∧ SecMaps w D.canonical D'.canonical :=
  ⟨fun h => (D.existsUnique_iso_of_idealSheaf_eq D' h).exists,
    fun ⟨_, hw⟩ => D.idealSheaf_eq_of_secMaps D' hw.2⟩

theorem exists_idealSheaf_eq {I : X.IdealSheafData} (hI : FinalTheorems.EffCartier I) :
    ∃ D : EffCartierData X, D.idealSheaf = I := by
  choose W g hx hg hI using hI
  have reg : ∀ x, IsRegularFn (g x) := fun x => (isRegularFn_iff_of_isAffineOpen (W x).2).2 (hg x)
  have st : ∀ x y (hy : y ∈ (W x).1),
      FinalTheorems.stalkId I y = Ideal.span {(X.presheaf.germ _ y hy).hom (g x)} := fun x y hy => by
    rw [ds_stalkId_eq_map _ (W x) y hy, hI, Ideal.map_span, Set.image_singleton]
  let D : EffCartierData X :=
    { ι := X
      U := fun x => (W x).1
      f := g
      cover := eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩
      regular := reg
      assoc := fun x x' => ((reg x).resG _).associated_of_germ ((reg x').resG _) fun y hy => by
        rw [germ_resG, germ_resG, ← st, ← st] }
  exact ⟨D, (D.eq_idealSheaf fun x => ⟨W x, x, le_rfl, hx x,
    (hI x).trans (congrArg (fun a => Ideal.span {a}) (resG_self _ _).symm)⟩).symm⟩

def ofSec {L : LB X} (hL : L.IsLB) (s : L.Sec) (hs : IsRegularSec s) : EffCartierData X where
  ι := L.ι
  U := L.U
  f := s.f
  cover := hL.cover
  regular := hs
  assoc i j := (congrArg (Associated · _) (s.compat i j)).mpr
    (associated_unit_mul_left _ _ (L.g i j).isUnit)

theorem lb_ofSec {L : LB X} (hL : L.IsLB) (s : L.Sec) (hs : IsRegularSec s) :
    (ofSec hL s hs).lb = L := by
  have : (ofSec hL s hs).trans = L.g := funext fun i => funext fun j =>
    ((ofSec hL s hs).eq_trans i j (s.compat i j)).symm
  exact congrArg (LB.mk L.ι L.U) this

theorem existsUnique_iso_ofSec {L : LB X} (hL : L.IsLB) (s : L.Sec) (hs : IsRegularSec s) :
    ∃! w : LB.Iso L (ofSec hL s hs).lb, w.IsGen ∧ SecMaps w s (ofSec hL s hs).canonical :=
  existsUnique_secMaps hs fun p q => ((ofSec hL s hs).assoc p q).symm

theorem existsUnique_iso_ofSec' {L : LB X} (hL : L.IsLB) (s : L.Sec) (hs : IsRegularSec s) :
    ∃! w : LB.Iso (ofSec hL s hs).lb L, w.IsGen ∧ SecMaps w (ofSec hL s hs).canonical s :=
  existsUnique_secMaps (A := (ofSec hL s hs).lb) hs fun p q => ((ofSec hL s hs).assoc p q).symm

theorem lbIso_ofSec {L : LB X} (hL : L.IsLB) (s : L.Sec) (hs : IsRegularSec s) :
    LBIso (ofSec hL s hs).lb L :=
  (existsUnique_iso_ofSec' hL s hs).exists.imp fun _ hw => hw.1

theorem ofSec_canonical : ofSec D.isLB_lb D.canonical D.isRegularSec_canonical = D := rfl

theorem coe_nonzeroLocus_eq_compl_support_ofSec {L : LB X} (hL : L.IsLB) (s : L.Sec)
    (hs : IsRegularSec s) :
    (Out.nonzeroLocus s : Set X) = ((ofSec hL s hs).idealSheaf.support : Set X)ᶜ :=
  (ofSec hL s hs).coe_nonzeroLocus_canonical

def KeepsRegular (φ : Y ⟶ X) : Prop := ∀ i, IsRegularFn ((φ.app (D.U i)).hom (D.f i))

theorem germ_app (φ : Y ⟶ X) {U : X.Opens} (a : Γ(X, U)) (y : Y) (hy : φ y ∈ U) :
    (Y.presheaf.germ (φ ⁻¹ᵁ U) y hy).hom ((φ.app U).hom a) =
      (φ.stalkMap y).hom ((X.presheaf.germ U (φ y) hy).hom a) :=
  (Scheme.Hom.germ_stalkMap_apply φ U y hy a).symm

theorem associated_germ_app (φ : Y ⟶ X) (i j : D.ι) (y : Y) (hi : y ∈ φ ⁻¹ᵁ D.U i)
    (hj : y ∈ φ ⁻¹ᵁ D.U j) :
    Associated ((Y.presheaf.germ _ y hi).hom ((φ.app (D.U i)).hom (D.f i)))
      ((Y.presheaf.germ _ y hj).hom ((φ.app (D.U j)).hom (D.f j))) := by
  rw [germ_app φ _ y hi, germ_app φ _ y hj]
  exact (D.associated_germ i j (φ y) hi hj).map _

theorem comap_idealSheaf (φ : Y ⟶ X) : D.idealSheaf.comap φ =
    locIdeal (fun i => φ ⁻¹ᵁ D.U i) (fun i => (φ.app (D.U i)).hom (D.f i))
      (fun y => D.exists_mem (φ y)) (D.associated_germ_app φ) := by
  apply le_antisymm
  · refine (comap_le_iff _ _ _).2 fun U a ha W h => (mem_locIdeal_iff _ _ _ _).2
      fun i y hy hi => ?_
    rw [germ_resG, germ_app φ _ y hi, germ_app φ a y (h hy)]
    exact map_dvd _ ((mem_locIdeal_iff _ _ _ _).1 ha i (φ y) (h hy) hi)
  · have loc : ∀ y : Y, ∃ (W : Y.affineOpens) (U : X.affineOpens) (i : D.ι),
        y ∈ W.1 ∧ W.1 ≤ φ ⁻¹ᵁ U.1 ∧ U.1 ≤ D.U i := fun y => by
      obtain ⟨i, hi⟩ := D.exists_mem (φ y)
      obtain ⟨U, hyU, hU⟩ := exists_affine_le hi
      obtain ⟨W, hyW, hW⟩ := exists_affine_le (V := φ ⁻¹ᵁ U.1) (x := y) hyU
      exact ⟨W, U, i, hyW, hW, hU⟩
    choose W U i hy hW hU using loc
    refine Scheme.IdealSheafData.le_of_iSup_eq_top W
      (eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hy y⟩) fun y => ?_
    refine (ideal_locIdeal (fun i => φ ⁻¹ᵁ D.U i) _ _ _ (W y) (i y)
      ((hW y).trans (φ.preimage_mono (hU y)))).trans_le ?_
    rw [Ideal.span_singleton_le_iff_mem]
    have := (comap_le_iff D.idealSheaf φ _).1 le_rfl (U y) (resG X (hU y) (D.f (i y)))
      (by rw [D.ideal_idealSheaf (U y) (i y) (hU y)]; exact Ideal.mem_span_singleton_self _)
      (W y) (hW y)
    rwa [app_resG, resG_resG] at this

theorem ideal_comap_idealSheaf (φ : Y ⟶ X) (W : Y.affineOpens) (i : D.ι)
    (h : W.1 ≤ φ ⁻¹ᵁ D.U i) :
    (D.idealSheaf.comap φ).ideal W = Ideal.span {resG Y h ((φ.app (D.U i)).hom (D.f i))} := by
  rw [comap_idealSheaf]
  exact ideal_locIdeal _ _ _ _ W i h

theorem keepsRegular_iff_effCartier (φ : Y ⟶ X) :
    D.KeepsRegular φ ↔ FinalTheorems.EffCartier (D.idealSheaf.comap φ) := by
  constructor
  · intro h y
    obtain ⟨i, hi⟩ := D.exists_mem (φ y)
    obtain ⟨W, hyW, hW⟩ := exists_affine_le (V := φ ⁻¹ᵁ D.U i) (x := y) hi
    exact ⟨W, _, hyW, h i _ hW, D.ideal_comap_idealSheaf φ W i hW⟩
  · intro h i
    refine isRegularFn_of_locally fun y hy => ?_
    obtain ⟨W, g, hyW, hg, hI⟩ := h y
    obtain ⟨W', hyW', hW'⟩ := exists_affine_le (V := W.1 ⊓ φ ⁻¹ᵁ D.U i) (x := y) ⟨hyW, hy⟩
    have h₁ : W'.1 ≤ W.1 := hW'.trans inf_le_left
    refine ⟨W'.1, hW'.trans inf_le_right, hyW', ?_⟩
    refine (((isRegularFn_iff_of_isAffineOpen W.2).2 hg).resG h₁).of_dvd ?_
    rw [← Ideal.mem_span_singleton, ← D.ideal_comap_idealSheaf φ W' i]
    exact (D.idealSheaf.comap φ).ideal_le_comap_ideal (U := W') (V := W) h₁
      (by rw [hI]; exact Ideal.mem_span_singleton_self _)

theorem keepsRegular_congr (h : D.idealSheaf = D'.idealSheaf) (φ : Y ⟶ X) :
    D.KeepsRegular φ ↔ D'.KeepsRegular φ := by
  rw [keepsRegular_iff_effCartier, keepsRegular_iff_effCartier, h]

theorem keepsRegular_iff_isRegularSec (φ : Y ⟶ X) :
    D.KeepsRegular φ ↔ IsRegularSec (secPull D.canonical φ) := by
  refine ⟨fun h j => (h (j ⟨⟩)).resG _, fun h i => ?_⟩
  have := (h fun _ => i).resG (pull_U D.lb φ fun _ => i).ge
  exact (congrArg IsRegularFn ((resG_resG _ _ _).trans (resG_self _ _))).mp this

theorem keepsRegular_of_flat (φ : Y ⟶ X) [Flat φ] : D.KeepsRegular φ :=
  fun i => (D.regular i).app_of_flat φ

theorem keepsRegular_of_notMem_support [IsIntegral Y] (φ : Y ⟶ X) {y : Y}
    (hy : φ y ∉ D.idealSheaf.support) : D.KeepsRegular φ := by
  obtain ⟨i, hi⟩ := D.exists_mem (φ y)
  refine (D.keepsRegular_iff_isRegularSec φ).2
    (isRegularSec_of_ne_zero _ (i := fun _ => i) fun h0 => ?_)
  have h1 : φ y ∈ Out.nonzeroLocus D.canonical := D.coe_nonzeroLocus_canonical.ge hy
  have h2 : y ∈ Out.nonzeroLocus (secPull D.canonical φ) :=
    (nonzeroLocus_secPull D.canonical φ).ge h1
  have h3 := (mem_nonzeroLocus_iff (secPull D.canonical φ) (fun _ => i)
    ((pull_U D.lb φ fun _ => i).ge hi)).1 h2
  rw [h0, Scheme.basicOpen_zero] at h3
  exact h3

theorem keepsRegular_of_isDominant [IsIntegral Y] (φ : Y ⟶ X) [IsDominant φ] :
    D.KeepsRegular φ := by
  have : Nonempty X := ⟨φ (genericPoint Y)⟩
  obtain ⟨y, hy⟩ := φ.denseRange.exists_mem_open (Out.nonzeroLocus D.canonical).isOpen
    D.dense_nonzeroLocus_canonical.nonempty
  exact D.keepsRegular_of_notMem_support φ (y := y) (D.coe_nonzeroLocus_canonical.le hy)

def pull (φ : Y ⟶ X) (h : D.KeepsRegular φ) : EffCartierData Y where
  ι := D.ι
  U i := φ ⁻¹ᵁ D.U i
  f i := (φ.app (D.U i)).hom (D.f i)
  cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 (D.exists_mem (φ y))
  regular := h
  assoc i j := by
    have := (D.assoc i j).map (φ.app (D.U i ⊓ D.U j)).hom
    rw [app_resG, app_resG] at this
    exact this

theorem idealSheaf_pull (φ : Y ⟶ X) (h : D.KeepsRegular φ) :
    (D.pull φ h).idealSheaf = D.idealSheaf.comap φ :=
  (D.comap_idealSheaf φ).symm

theorem existsUnique_iso_pull (φ : Y ⟶ X) (h : D.KeepsRegular φ) :
    ∃! w : LB.Iso (D.pull φ h).lb (D.lb.pull φ),
      w.IsGen ∧ SecMaps w (D.pull φ h).canonical (secPull D.canonical φ) :=
  existsUnique_secMaps (D.pull φ h).regular fun p q => by
    have := ((D.pull φ h).assoc q (p ⟨⟩)).map (resG Y
      (le_inf inf_le_right (inf_le_left.trans (pull_U D.lb φ p).le) :
        (D.lb.pull φ).U p ⊓ (D.pull φ h).U q ≤ (D.pull φ h).U q ⊓ (D.pull φ h).U (p ⟨⟩)))
    rw [resG_resG, resG_resG] at this
    exact (congrArg (Associated _) (resG_resG _ _ _)).mpr this

theorem lbIso_pull (φ : Y ⟶ X) (h : D.KeepsRegular φ) : LBIso (D.pull φ h).lb (D.lb.pull φ) :=
  (D.existsUnique_iso_pull φ h).exists.imp fun _ hw => hw.1

theorem keepsRegular_comp_iff (φ : Y ⟶ X) (h : D.KeepsRegular φ) (ψ : Z ⟶ Y) :
    D.KeepsRegular (ψ ≫ φ) ↔ (D.pull φ h).KeepsRegular ψ := Iff.rfl

theorem pull_comp (φ : Y ⟶ X) (h : D.KeepsRegular φ) (ψ : Z ⟶ Y)
    (h' : (D.pull φ h).KeepsRegular ψ) :
    D.pull (ψ ≫ φ) ((D.keepsRegular_comp_iff φ h ψ).2 h') = (D.pull φ h).pull ψ h' := rfl

theorem pull_id : D.pull (𝟙 X) (D.keepsRegular_of_flat _) = D := rfl

def add : EffCartierData X where
  ι := D.ι × D'.ι
  U p := D.U p.1 ⊓ D'.U p.2
  f p := resG X inf_le_left (D.f p.1) * resG X inf_le_right (D'.f p.2)
  cover := eq_top_iff.2 fun x _ => by
    obtain ⟨i, hi⟩ := D.exists_mem x
    obtain ⟨j, hj⟩ := D'.exists_mem x
    exact Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  regular p := ((D.regular p.1).resG _).mul ((D'.regular p.2).resG _)
  assoc p q := by
    have h₁ := (D.assoc p.1 q.1).map (resG X (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left) :
        D.U p.1 ⊓ D'.U p.2 ⊓ (D.U q.1 ⊓ D'.U q.2) ≤ D.U p.1 ⊓ D.U q.1))
    have h₂ := (D'.assoc p.2 q.2).map (resG X (le_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right) :
        D.U p.1 ⊓ D'.U p.2 ⊓ (D.U q.1 ⊓ D'.U q.2) ≤ D'.U p.2 ⊓ D'.U q.2))
    rw [resG_resG, resG_resG] at h₁ h₂
    rw [map_mul, map_mul, resG_resG, resG_resG, resG_resG, resG_resG]
    exact h₁.mul_mul h₂

theorem resG_add_f (i : D.ι) (j : D'.ι) {W : X.Opens} (h : W ≤ D.U i ⊓ D'.U j) :
    resG X h ((D.add D').f (i, j)) =
      resG X (h.trans inf_le_left) (D.f i) * resG X (h.trans inf_le_right) (D'.f j) := by
  refine (map_mul (resG X h) _ _).trans ?_
  rw [resG_resG, resG_resG]

theorem idealSheaf_add : (D.add D').idealSheaf = D.idealSheaf * D'.idealSheaf := by
  refine ((D.add D').eq_idealSheaf fun x => ?_).symm
  obtain ⟨i, hi⟩ := D.exists_mem x
  obtain ⟨j, hj⟩ := D'.exists_mem x
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := D.U i ⊓ D'.U j) ⟨hi, hj⟩
  refine ⟨W, (i, j), hW, hxW, ?_⟩
  change D.idealSheaf.ideal W * D'.idealSheaf.ideal W = _
  rw [D.ideal_idealSheaf W i (hW.trans inf_le_left), D'.ideal_idealSheaf W j (hW.trans inf_le_right),
    Ideal.span_singleton_mul_span_singleton]
  exact congrArg (fun a => Ideal.span {a}) (D.resG_add_f D' i j hW).symm

theorem res_trans_add (p q : D.ι × D'.ι) {W : X.Opens} (hp : W ≤ D.U p.1 ⊓ D'.U p.2)
    (hq : W ≤ D.U q.1 ⊓ D'.U q.2) :
    res (le_inf hp hq) ((D.add D').trans p q) =
      res (le_inf (hp.trans inf_le_left) (hq.trans inf_le_left)) (D.trans p.1 q.1) *
        res (le_inf (hp.trans inf_le_right) (hq.trans inf_le_right)) (D'.trans p.2 q.2) := by
  refine Units.ext ((D.add D').eq_trans_on p q hp hq ?_).symm
  refine (D.resG_add_f D' p.1 p.2 hp).trans (Eq.trans ?_
    (congrArg _ (D.resG_add_f D' q.1 q.2 hq)).symm)
  rw [D.trans_spec_on p.1 q.1 _ (hq.trans inf_le_left),
    D'.trans_spec_on p.2 q.2 _ (hq.trans inf_le_right), mul_mul_mul_comm]
  rfl

def addGen : LB.Gen (LB.div (LB.div (D.add D').lb D.lb) D'.lb) where
  s := fun p : ((D.ι × D'.ι) × D.ι) × D'.ι =>
    (res (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans inf_le_right)) (D.trans p.1.1.1 p.1.2) *
      res (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right)) inf_le_right)
        (D'.trans p.1.1.2 p.2) : Γ(X, D.U p.1.1.1 ⊓ D'.U p.1.1.2 ⊓ D.U p.1.2 ⊓ D'.U p.2)ˣ)

theorem res_addGen (i j : D.ι) (i' j' : D'.ι) {W : X.Opens}
    (h : W ≤ D.U i ⊓ D'.U i' ⊓ D.U j ⊓ D'.U j') :
    res h ((D.addGen D').s (((i, i'), j), j')) =
      res (le_inf (h.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
        (h.trans (inf_le_left.trans inf_le_right))) (D.trans i j) *
      res (le_inf (h.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
        (h.trans inf_le_right)) (D'.trans i' j') := by
  refine (map_mul (res h) _ _).trans ?_
  rw [LB.res_res, LB.res_res]

theorem addGen_canonical (i j : D.ι) (i' j' : D'.ι) {W : X.Opens}
    (h : W ≤ D.U i ⊓ D'.U i' ⊓ D.U j ⊓ D'.U j') :
    resG X (h.trans (inf_le_left.trans inf_le_left)) ((D.add D').canonical.f (i, i')) =
      (res h ((D.addGen D').s (((i, i'), j), j')) : Γ(X, W)ˣ) *
        (resG X (h.trans (inf_le_left.trans inf_le_right)) (D.canonical.f j) *
          resG X (h.trans inf_le_right) (D'.canonical.f j')) := by
  refine (D.resG_add_f D' i i' _).trans ?_
  rw [res_addGen, D.trans_spec_on i j _ (h.trans (inf_le_left.trans inf_le_right)),
    D'.trans_spec_on i' j' _ (h.trans inf_le_right), mul_mul_mul_comm]
  rfl

theorem isGen_of_mul {N L M : LB X} {a : L.Sec} {b : M.Sec} {c : N.Sec} (ha : IsRegularSec a)
    (hb : IsRegularSec b) (w : LB.Gen (LB.div (LB.div N L) M))
    (H : ∀ (i : N.ι) (j : L.ι) (k : M.ι) {W : X.Opens} (h : W ≤ N.U i ⊓ L.U j ⊓ M.U k),
      resG X (h.trans (inf_le_left.trans inf_le_left)) (c.f i) =
        (res h (w.s ((i, j), k)) : Γ(X, W)ˣ) *
          (resG X (h.trans (inf_le_left.trans inf_le_right)) (a.f j) *
            resG X (h.trans inf_le_right) (b.f k))) : w.IsGen := by
  rintro ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩
  have key : ∀ {W : X.Opens} (h : W ≤ N.U i ⊓ L.U j ⊓ M.U k) (h' : W ≤ N.U i' ⊓ L.U j' ⊓ M.U k'),
      res h (w.s ((i, j), k)) =
        res (le_inf (h.trans (inf_le_left.trans inf_le_left))
          (h'.trans (inf_le_left.trans inf_le_left))) (N.g i i') *
        (res (le_inf (h.trans (inf_le_left.trans inf_le_right))
          (h'.trans (inf_le_left.trans inf_le_right))) (L.g j j'))⁻¹ *
        (res (le_inf (h.trans inf_le_right) (h'.trans inf_le_right)) (M.g k k'))⁻¹ *
        res h' (w.s ((i', j'), k')) := by
    intro W h h'
    rw [mul_right_comm, mul_right_comm _ _⁻¹, eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq]
    refine Units.ext ((((ha j').resG (h'.trans (inf_le_left.trans inf_le_right))).mul
      ((hb k').resG (h'.trans inf_le_right))).mul_right_cancel ?_)
    have e₁ := H i j k h
    have e₂ := H i' j' k' h'
    rw [sec_compat c i i' _ (h'.trans (inf_le_left.trans inf_le_left)), e₂,
      sec_compat a j j' _ (h'.trans (inf_le_left.trans inf_le_right)),
      sec_compat b k k' _ (h'.trans inf_le_right)] at e₁
    simp only [Units.val_mul, val_res] at e₁ ⊢
    linear_combination -e₁
  refine (key inf_le_left inf_le_right).trans (congrArg (· * _) (congrArg (· * _) ?_))
  exact (LB.res_dg N L (i, j) (i', j') _).symm

theorem isGen_addGen : (D.addGen D').IsGen :=
  isGen_of_mul (c := (D.add D').canonical) D.isRegularSec_canonical D'.isRegularSec_canonical _
    fun i j j' _ h => D.addGen_canonical D' i.1 j i.2 j' h

theorem lbIso_add : LBIso D'.lb (LB.div (D.add D').lb D.lb) := ⟨D.addGen D', D.isGen_addGen D'⟩

theorem app_add_f (φ : Y ⟶ X) (p : D.ι × D'.ι) :
    (φ.app ((D.add D').U p)).hom ((D.add D').f p) =
      resG Y (φ.preimage_mono inf_le_left) ((φ.app (D.U p.1)).hom (D.f p.1)) *
        resG Y (φ.preimage_mono inf_le_right) ((φ.app (D'.U p.2)).hom (D'.f p.2)) :=
  (map_mul (φ.app (D.U p.1 ⊓ D'.U p.2)).hom _ _).trans
    (congrArg₂ (· * ·) (app_resG φ _ _) (app_resG φ _ _))

theorem KeepsRegular.add {D D' : EffCartierData X} {φ : Y ⟶ X} (h : D.KeepsRegular φ)
    (h' : D'.KeepsRegular φ) : (D.add D').KeepsRegular φ := fun p =>
  (congrArg IsRegularFn (D.app_add_f D' φ p)).mpr (((h p.1).resG _).mul ((h' p.2).resG _))

theorem pull_add (φ : Y ⟶ X) (h : D.KeepsRegular φ) (h' : D'.KeepsRegular φ) :
    (D.add D').pull φ (h.add h') = (D.pull φ h).add (D'.pull φ h') := by
  have key : ∀ (A : EffCartierData Y) (f : ∀ i, Γ(Y, A.U i)) (r) (a), f = A.f →
      EffCartierData.mk A.ι A.U f A.cover r a = A := by
    rintro A f r a rfl
    rfl
  exact key ((D.pull φ h).add (D'.pull φ h')) _ _ _ (funext (D.app_add_f D' φ))

def nsmul (n : ℕ) : EffCartierData X where
  ι := D.ι
  U := D.U
  f i := D.f i ^ n
  cover := D.cover
  regular i := (D.regular i).pow n
  assoc i j := by
    rw [map_pow, map_pow]
    exact (D.assoc i j).pow_pow

theorem idealSheaf_nsmul (n : ℕ) : (D.nsmul n).idealSheaf = D.idealSheaf ^ n := by
  refine ((D.nsmul n).eq_idealSheaf fun x => ?_).symm
  obtain ⟨i, hi⟩ := D.exists_mem x
  obtain ⟨W, hxW, hW⟩ := exists_affine_le hi
  refine ⟨W, i, hW, hxW, ?_⟩
  change D.idealSheaf.ideal W ^ n = _
  rw [D.ideal_idealSheaf W i hW, Ideal.span_singleton_pow, ← map_pow]
  rfl

theorem existsUnique_iso_nsmul (n : ℕ) :
    ∃! w : LB.Iso (D.nsmul n).lb (lbPow D.lb n),
      w.IsGen ∧ SecMaps w (D.nsmul n).canonical (secPow D.canonical n) :=
  existsUnique_secMaps (D.nsmul n).regular fun p q => by
    have := ((D.nsmul n).assoc q (p ⟨⟩)).map (resG X
      (le_inf inf_le_right (inf_le_left.trans (lbPow_U D.lb n p).le) :
        (lbPow D.lb n).U p ⊓ (D.nsmul n).U q ≤ (D.nsmul n).U q ⊓ (D.nsmul n).U (p ⟨⟩)))
    rw [resG_resG, resG_resG] at this
    refine (congrArg (Associated _) ?_).mpr this
    exact (congrArg _ (map_pow (resG X (lbPow_U D.lb n p).le) _ n).symm).trans (resG_resG _ _ _)

theorem lbIso_nsmul (n : ℕ) : LBIso (D.nsmul n).lb (lbPow D.lb n) :=
  (D.existsUnique_iso_nsmul n).exists.imp fun _ hw => hw.1

theorem idealSheaf_principal (a : Γ(X, ⊤)) (ha : IsRegularFn a) :
    (principal a ha).idealSheaf = Scheme.IdealSheafData.ofIdealTop (Ideal.span {a}) := by
  ext W : 2
  rw [(principal a ha).ideal_idealSheaf W ⟨⟩ le_top, Scheme.IdealSheafData.ofIdealTop_ideal,
    Ideal.map_span, Set.image_singleton]
  rfl

theorem lb_principal (a : Γ(X, ⊤)) (ha : IsRegularFn a) : (principal a ha).lb = LB.triv X := by
  have : (principal a ha).trans = fun _ _ => 1 := funext fun i => funext fun j =>
    ((principal a ha).eq_trans i j (u := 1) (one_mul _).symm).symm
  exact congrArg (LB.mk PUnit fun _ => ⊤) this

theorem idealSheaf_zero : (zero X).idealSheaf = ⊤ := by
  ext W : 2
  rw [(zero X).ideal_idealSheaf W ⟨⟩ le_top]
  exact Ideal.span_singleton_eq_top.2 (isUnit_one.map _)

section Rational

variable [IsIntegral X]

def poleSecs (n : ℕ) (V : X.Opens) [Nonempty V] : Submodule Γ(X, V) X.functionField :=
  ratSecs (D.nsmul n).canonical V

theorem mem_poleSecs_iff (n : ℕ) (V : X.Opens) [Nonempty V] (h : X.functionField) :
    h ∈ D.poleSecs n V ↔ ∀ (i : D.ι) [Nonempty (V ⊓ D.U i : X.Opens)], ∃ a : Γ(X, V ⊓ D.U i),
      (X.germToFunctionField _).hom a =
        (X.germToFunctionField (V ⊓ D.U i)).hom (resG X inf_le_right (D.f i)) ^ n * h := by
  refine forall₂_congr fun i _ => exists_congr fun a => iff_of_eq (congrArg (fun r => _ = r * h) ?_)
  exact (congrArg _ (map_pow (resG X _) (D.f i) n)).trans (map_pow _ _ n)

theorem mem_poleSecs_iff_stalk (n : ℕ) (V : X.Opens) [Nonempty V] (h : X.functionField) :
    h ∈ D.poleSecs n V ↔ ∀ (i : D.ι) (x : X) (_ : x ∈ V) (hx : x ∈ D.U i),
      algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ _ x hx).hom (D.f i)) ^ n *
        h ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  refine (mem_ratSecs_iff_stalk _ V h).trans (forall₄_congr fun i x _ hx => iff_of_eq
    (congrArg (fun r => r * h ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) ?_))
  exact (congrArg _ (map_pow (X.presheaf.germ _ x hx).hom (D.f i) n)).trans (map_pow _ _ n)

theorem poleSecs_congr (h : D.idealSheaf = D'.idealSheaf) (n : ℕ) (V : X.Opens) [Nonempty V] :
    D.poleSecs n V = D'.poleSecs n V := by
  obtain ⟨w, -, hw⟩ := ((D.nsmul n).idealSheaf_eq_iff (D'.nsmul n)).1
    (by rw [idealSheaf_nsmul, idealSheaf_nsmul, h])
  exact hw.ratSecs_eq (D.nsmul n).isLB_lb (D'.nsmul n).isLB_lb V

theorem mem_poleSecs_zero_iff (V : X.Opens) [Nonempty V] (h : X.functionField) :
    h ∈ D.poleSecs 0 V ↔ ∃ a : Γ(X, V), (X.germToFunctionField V).hom a = h := by
  rw [mem_poleSecs_iff_stalk]
  constructor
  · intro H
    refine exists_germK_eq_of_stalk V h fun x hx => ?_
    obtain ⟨i, hi⟩ := D.exists_mem x
    simpa using H i x hx hi
  · rintro ⟨a, rfl⟩ i x hx hi
    rw [pow_zero, one_mul]
    exact ⟨_, Scheme.algebraMap_germ_eq_germToFunctionField X hx a⟩

theorem poleSecs_mono (V : X.Opens) [Nonempty V] : Monotone fun n => D.poleSecs n V := by
  refine monotone_nat_of_le_succ fun n h hh => ?_
  rw [mem_poleSecs_iff_stalk] at hh ⊢
  intro i x hx hi
  obtain ⟨r, hr⟩ := hh i x hx hi
  exact ⟨(X.presheaf.germ _ x hi).hom (D.f i) * r, by rw [map_mul, hr]; ring⟩

theorem mul_mem_poleSecs {m n : ℕ} {V : X.Opens} [Nonempty V] {h h' : X.functionField}
    (hh : h ∈ D.poleSecs m V) (hh' : h' ∈ D.poleSecs n V) : h * h' ∈ D.poleSecs (m + n) V := by
  rw [mem_poleSecs_iff_stalk] at hh hh' ⊢
  intro i x hx hi
  obtain ⟨r, hr⟩ := hh i x hx hi
  obtain ⟨r', hr'⟩ := hh' i x hx hi
  exact ⟨r * r', by rw [map_mul, hr, hr']; ring⟩

theorem bijOn_poleSecs_nsmul (n : ℕ) (V : X.Opens) [Nonempty V] :
    Set.BijOn (ratOf (D.nsmul n).isLB_lb (D.nsmul n).canonical V) (secOn (D.nsmul n).lb V)
      (D.poleSecs n V) :=
  bijOn_ratOf _ (D.nsmul n).isRegularSec_canonical V

theorem germK_eq_pow_mul_ratOf (n : ℕ) (V : X.Opens) [Nonempty V]
    {t : ∀ i, Γ(X, V ⊓ (D.nsmul n).lb.U i)} (ht : t ∈ secOn (D.nsmul n).lb V) (i : D.ι)
    [hi : Nonempty (V ⊓ D.U i : X.Opens)] :
    (X.germToFunctionField (V ⊓ D.U i)).hom (t i) =
      (X.germToFunctionField (V ⊓ D.U i)).hom (resG X inf_le_right (D.f i)) ^ n *
        ratOf (D.nsmul n).isLB_lb (D.nsmul n).canonical V t := by
  refine (@germK_eq_mul_ratOf _ _ _ (D.nsmul n).isLB_lb _ (D.nsmul n).isRegularSec_canonical V _ _
    ht i hi).trans (congrArg (· * _) ?_)
  exact (congrArg _ (map_pow (resG X _) (D.f i) n)).trans (map_pow _ _ n)

theorem isLB_lbPow {X : Scheme.{0}} (D : EffCartierData X) (n : ℕ) : (lbPow D.lb n).IsLB :=
  LB.isLB_linComb D.isLB_lb _ _

theorem bijOn_poleSecs_lbPow (n : ℕ) (V : X.Opens) [Nonempty V] :
    Set.BijOn (ratOf (D.isLB_lbPow n) (secPow D.canonical n) V) (secOn (lbPow D.lb n) V)
      (D.poleSecs n V) := by
  obtain ⟨w, ⟨-, hw⟩, -⟩ := D.existsUnique_iso_nsmul n
  rw [poleSecs, hw.ratSecs_eq (D.nsmul n).isLB_lb (D.isLB_lbPow n) V]
  exact bijOn_ratOf _ (D.isRegularSec_canonical.secPow n) V

theorem bijOn_poleSecs_one (V : X.Opens) [Nonempty V] :
    Set.BijOn (ratOf D.isLB_lb D.canonical V) (secOn D.lb V) (D.poleSecs 1 V) := by
  obtain ⟨w, -, hw⟩ := ((D.nsmul 1).idealSheaf_eq_iff D).1 (by rw [idealSheaf_nsmul, pow_one])
  rw [poleSecs, hw.ratSecs_eq (D.nsmul 1).isLB_lb D.isLB_lb V]
  exact bijOn_ratOf _ D.isRegularSec_canonical V

theorem germK_eq_pow_mul_ratOf_lbPow (n : ℕ) (V : X.Opens) [Nonempty V]
    {t : ∀ j, Γ(X, V ⊓ (lbPow D.lb n).U j)} (ht : t ∈ secOn (lbPow D.lb n) V) (j : PUnit → D.ι)
    [hj : Nonempty (V ⊓ (lbPow D.lb n).U j : X.Opens)] :
    (X.germToFunctionField (V ⊓ (lbPow D.lb n).U j)).hom (t j) =
      (X.germToFunctionField (V ⊓ (lbPow D.lb n).U j)).hom
        (resG X (inf_le_right.trans (lbPow_U D.lb n j).le) (D.f (j ⟨⟩))) ^ n *
        ratOf (D.isLB_lbPow n) (secPow D.canonical n) V t := by
  refine (@germK_eq_mul_ratOf _ _ _ (D.isLB_lbPow n) _ (D.isRegularSec_canonical.secPow n) V _ _
    ht j hj).trans (congrArg (· * _) ?_)
  exact (congrArg _ ((map_pow (resG X _) _ n).trans (congrArg (· ^ n) (resG_resG _ _ _)))).trans
    (map_pow _ _ n)

theorem bijOn_poleSecs_global (n : ℕ) :
    Set.BijOn (fun t => ratOf (D.isLB_lbPow n) (secPow D.canonical n) ⊤ (secOnOf t ⊤)) Set.univ
      (D.poleSecs n ⊤) :=
  (D.bijOn_poleSecs_lbPow n ⊤).comp (bijOn_secOnOf_top _)

theorem ratOf_secPow_canonical (n : ℕ) (V : X.Opens) [Nonempty V] :
    ratOf (D.isLB_lbPow n) (secPow D.canonical n) V (secOnOf (secPow D.canonical n) V) = 1 :=
  ratOf_secOnOf_self _ (D.isRegularSec_canonical.secPow n) V

theorem mem_poleSecs_principal_iff (a : Γ(X, ⊤)) (ha : IsRegularFn a) (n : ℕ) (V : X.Opens)
    [Nonempty V] (h : X.functionField) :
    h ∈ (principal a ha).poleSecs n V ↔ ∃ b : Γ(X, V), (X.germToFunctionField V).hom b =
      (X.germToFunctionField V).hom (resG X le_top a) ^ n * h := by
  have e : ∀ x (hx : x ∈ V), algebraMap (X.presheaf.stalk x) X.functionField
      ((X.presheaf.germ ⊤ x trivial).hom a) = (X.germToFunctionField V).hom (resG X le_top a) :=
    fun x hx => (congrArg _ (germ_resG le_top x hx a).symm).trans
      (Scheme.algebraMap_germ_eq_germToFunctionField X hx _)
  rw [mem_poleSecs_iff_stalk]
  constructor
  · intro H
    refine exists_germK_eq_of_stalk V _ fun x hx => ?_
    rw [← e x hx]
    exact H ⟨⟩ x hx trivial
  · rintro ⟨b, hb⟩ i x hx hi
    refine ⟨_, (Scheme.algebraMap_germ_eq_germToFunctionField X hx b).trans (hb.trans ?_)⟩
    rw [← e x hx]
    rfl

end Rational

theorem mem_support_ofElement_iff {R : Type} [CommRing R] (r : R) (hr : r ∈ nonZeroDivisors R)
    (p : PrimeSpectrum R) :
    (p : Sp R) ∈ (ofElement r hr).idealSheaf.support ↔ r ∈ p.asIdeal := by
  refine ((ofElement r hr).mem_support_iff ⟨⟩ (x := p) trivial).trans ?_
  have e := basicOpen_eq_of_affine (R := CommRingCat.of R) r
  exact (not_congr (iff_of_eq (congrArg (fun W => (p : Sp R) ∈ W) e))).trans not_not

example : (⟨Ideal.span {Polynomial.X}, (Ideal.span_singleton_prime Polynomial.X_ne_zero).2
    Polynomial.prime_X⟩ : PrimeSpectrum (Polynomial ℤ)) ∈ lineOrigin.idealSheaf.support :=
  (mem_support_ofElement_iff _ _ _).2 (Ideal.mem_span_singleton_self _)

example : (⊥ : PrimeSpectrum (Polynomial ℤ)) ∉ lineOrigin.idealSheaf.support :=
  fun h => Polynomial.X_ne_zero ((mem_support_ofElement_iff _ _ _).1 h)

example (a : Γ(X, ⊤)) (ha : IsRegularFn a) (u : Γ(X, ⊤)ˣ) :
    (principalTwist a ha u).lb.g true false = res (inf_le_left : (⊤ : X.Opens) ⊓ ⊤ ≤ ⊤) u :=
  ((principalTwist a ha u).eq_trans true false (map_mul (resG X _) _ _)).symm

example (t : (Sp (Polynomial ℤ)).functionField)
    (ht : t = ((Sp (Polynomial ℤ)).germToFunctionField ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X)) :
    t⁻¹ ∈ lineOrigin.poleSecs 1 ⊤ ∧ t⁻¹ ∉ lineOrigin.poleSecs 0 ⊤ := by
  have h0 : t ≠ 0 := ht ▸ nonZeroDivisors.ne_zero
    (isRegularFn_iff_germ.1 (lineOrigin.regular ⟨⟩) _ trivial)
  have hh : t * t⁻¹ = 1 := mul_inv_cancel₀ h0
  constructor
  · refine (mem_poleSecs_principal_iff _ _ 1 ⊤ _).2 ⟨1, ?_⟩
    rw [map_one, pow_one, resG_self, ← ht, hh]
  · intro H
    obtain ⟨b, hb⟩ := (mem_poleSecs_zero_iff _ ⊤ _).1 H
    rw [← hb, ht, ← map_mul, ← map_one ((Sp (Polynomial ℤ)).germToFunctionField ⊤).hom] at hh
    have e := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).hom.hom
      ((Sp (Polynomial ℤ)).germToFunctionField_injective ⊤ hh)
    rw [map_mul, map_one, Iso.inv_hom_id_apply] at e
    exact Polynomial.not_isUnit_X (IsUnit.of_mul_eq_one _ e)

example : ¬ lineOrigin.KeepsRegular (spMap (Polynomial.evalRingHom (0 : ℤ))) := fun h => by
  have hd := (lineOrigin.pull _ h).dense_nonzeroLocus_canonical
  have : Nonempty (Sp ℤ) := ⟨(⊥ : PrimeSpectrum ℤ)⟩
  obtain ⟨p, hp⟩ := hd.nonempty
  rw [coe_nonzeroLocus_canonical, idealSheaf_pull, Scheme.IdealSheafData.support_comap] at hp
  refine hp ((mem_support_ofElement_iff _ _ _).2 ?_)
  change Polynomial.evalRingHom (0 : ℤ) Polynomial.X ∈ PrimeSpectrum.asIdeal p
  simp

end EffCartierData

end GlobalTheory
