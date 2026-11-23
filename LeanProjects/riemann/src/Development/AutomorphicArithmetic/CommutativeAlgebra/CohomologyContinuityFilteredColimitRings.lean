import Mathlib
import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace UpperTheory.DirectSumIndependence

private abbrev P (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    Ht q (sch.obj (Spec A)) n i →+ Ht q (sch.obj (Spec B)) n i :=
  pull _ (sch.map (Spec.map f)) (tw q i) n

private theorem pullback_comp₂ (q : ℕ) (i n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (x : Ht q (sch.obj (Spec A)) n i) : P q i n (f ≫ g) x = P q i n g (P q i n f x) := by
  show pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n x = _
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

private theorem isUnit_of_hom {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (h : IsUnit (q : A)) :
    IsUnit (q : B) := by
  simpa using h.map f.hom

private theorem chase (b1 : B1) (q : ℕ) (i : ℤ) {J : Type} [SmallCategory J] [IsFiltered J]
    (D D' : J ⥤ CommRingCat.{0}) (α : D ⟶ D') (c : Cocone D) (hc : IsColimit c)
    (c' : Cocone D') (hc' : IsColimit c') (g : c.pt ⟶ c'.pt)
    (hg : ∀ j, c.ι.app j ≫ g = α.app j ≫ c'.ι.app j)
    (hα : ∀ j, RE q i (α.app j)) (hq : ∀ j, IsUnit (q : D.obj j)) : RE q i g := by
  intro n
  change Function.Bijective (P q i n g)
  have hqc : IsUnit (q : c.pt) := by
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    exact isUnit_of_hom (c.ι.app j) (hq j)
  have hqc' : IsUnit (q : c'.pt) := isUnit_of_hom g hqc
  have hqD' : ∀ j, IsUnit (q : D'.obj j) := fun j => isUnit_of_hom (α.app j) (hq j)
  have comm : ∀ j y, P q i n g (P q i n (c.ι.app j) y) =
      P q i n (c'.ι.app j) (P q i n (α.app j) y) := by
    intro j y
    rw [← pullback_comp₂, ← pullback_comp₂, hg]
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, hy⟩ := (b1 q D c hc n i).1 x hqc
    change P q i n (c.ι.app j) y = x at hy
    subst hy
    rw [comm] at hx
    obtain ⟨k, f, hf⟩ := (b1 q D' c' hc' n i).2 j (P q i n (α.app j) y) (hqD' j) hx
    change P q i n (D'.map f) (P q i n (α.app j) y) = 0 at hf
    rw [← pullback_comp₂, ← α.naturality f, pullback_comp₂] at hf
    have h0 : P q i n (D.map f) y = 0 := by
      apply (hα k n).1
      show P q i n (α.app k) (P q i n (D.map f) y) = P q i n (α.app k) 0
      rw [hf, map_zero]
    rw [← c.w f, pullback_comp₂, h0, map_zero]
  · intro z
    obtain ⟨j, y', hy'⟩ := (b1 q D' c' hc' n i).1 z hqc'
    change P q i n (c'.ι.app j) y' = z at hy'
    obtain ⟨y, rfl⟩ := (hα j n).2 y'
    refine ⟨P q i n (c.ι.app j) y, ?_⟩
    rw [← hy']
    exact comm j y

variable {J : Type} [SmallCategory J] {A Y : CommRingCat.{0}} (φ : A ⟶ Y) (D : J ⥤ CommRingCat.{0})
  (t : ∀ j, A ⟶ D.obj j) (ht : ∀ {j k : J} (f : j ⟶ k), t j ≫ D.map f = t k)

private def Dp : J ⥤ CommRingCat.{0} where
  obj j := pushout φ (t j)
  map {j k} f := pushout.desc (pushout.inl φ (t k)) (D.map f ≫ pushout.inr φ (t k)) (by
    rw [← Category.assoc, ht f, pushout.condition])
  map_id j := by
    apply pushout.hom_ext <;> simp
  map_comp {j k l} f g := by
    apply pushout.hom_ext
    · erw [pushout.inl_desc, ← Category.assoc, pushout.inl_desc, pushout.inl_desc]
    · erw [pushout.inr_desc, ← Category.assoc, pushout.inr_desc, Category.assoc, pushout.inr_desc,
        D.map_comp, Category.assoc]

private theorem inl_Dp {j k : J} (f : j ⟶ k) :
    pushout.inl φ (t j) ≫ (Dp φ D t ht).map f = pushout.inl φ (t k) :=
  pushout.inl_desc _ _ _

private theorem inr_Dp {j k : J} (f : j ⟶ k) :
    pushout.inr φ (t j) ≫ (Dp φ D t ht).map f = D.map f ≫ pushout.inr φ (t k) :=
  pushout.inr_desc _ _ _

private def toDp : D ⟶ Dp φ D t ht where
  app j := pushout.inr φ (t j)
  naturality j k f := (inr_Dp φ D t ht f).symm

variable (c : Cocone D) (hc : IsColimit c) {Y' : CommRingCat.{0}} (w : Y ⟶ Y') (φ' : c.pt ⟶ Y')
  (cc : A ⟶ c.pt) (hcc : ∀ j, t j ≫ c.ι.app j = cc) (hp : IsPushout φ cc w φ')

private def cocDp : Cocone (Dp φ D t ht) where
  pt := Y'
  ι :=
    { app j := pushout.desc w (c.ι.app j ≫ φ') (by
        rw [← Category.assoc, hcc, hp.w])
      naturality j k f := by
        refine pushout.hom_ext ?_ ?_
        · erw [← Category.assoc, inl_Dp, pushout.inl_desc, ← Category.assoc, pushout.inl_desc,
            Category.comp_id]
        · erw [← Category.assoc, inr_Dp, Category.assoc, pushout.inr_desc, ← Category.assoc, c.w f,
            ← Category.assoc, pushout.inr_desc, Category.comp_id] }

private theorem inl_coc (j : J) :
    pushout.inl φ (t j) ≫ (cocDp φ D t ht c w φ' cc hcc hp).ι.app j = w :=
  pushout.inl_desc _ _ _

private theorem inr_coc (j : J) :
    pushout.inr φ (t j) ≫ (cocDp φ D t ht c w φ' cc hcc hp).ι.app j = c.ι.app j ≫ φ' :=
  pushout.inr_desc _ _ _

private theorem inl_indep [IsFiltered J] (e : Cocone (Dp φ D t ht)) (j k : J) :
    pushout.inl φ (t j) ≫ e.ι.app j = pushout.inl φ (t k) ≫ e.ι.app k := by
  rw [← e.w (IsFiltered.leftToMax j k), ← e.w (IsFiltered.rightToMax j k)]
  erw [← Category.assoc, inl_Dp, ← Category.assoc, inl_Dp]

private def resCoc (e : Cocone (Dp φ D t ht)) : Cocone D where
  pt := e.pt
  ι :=
    { app j := pushout.inr φ (t j) ≫ e.ι.app j
      naturality j k f := by
        erw [Category.comp_id, ← e.w f, ← Category.assoc, ← Category.assoc, inr_Dp]
        simp
        rfl }

private def isColDp [IsFiltered J] : IsColimit (cocDp φ D t ht c w φ' cc hcc hp) :=
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  { desc := fun e => hp.desc (pushout.inl φ (t j0) ≫ e.ι.app j0)
      (hc.desc (resCoc φ D t ht e)) (by
        erw [← hcc j0, Category.assoc, hc.fac, ← Category.assoc, pushout.condition, Category.assoc])
    fac := fun e j => by
      refine pushout.hom_ext ?_ ?_
      · erw [← Category.assoc, inl_coc, hp.inl_desc]
        exact inl_indep φ D t ht e j0 j
      · erw [← Category.assoc, inr_coc, Category.assoc, hp.inr_desc, hc.fac]
        rfl
    uniq := fun e m hm => by
      refine hp.hom_ext ?_ ?_
      · erw [hp.inl_desc, ← hm j0, ← Category.assoc, inl_coc]
        rfl
      · erw [hp.inr_desc]
        refine hc.hom_ext fun j => ?_
        erw [hc.fac, ← Category.assoc, ← inr_coc φ D t ht c w φ' cc hcc hp j, Category.assoc, hm j]
        rfl }

end UpperTheory.DirectSumIndependence

theorem UpperTheory.cohomology_continuity_filtered_colimit_rings :
    LateralTheory.E.t_E3Cut.Limit := by
  intro hyp q _ i A Y φ hq hEt C c hc Y' w φ' hp
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hc
  have ht : ∀ {j k : J} (f : j ⟶ k), t.app j ≫ D.map f = t.app k := by
    intro j k f
    rw [← t.naturality f]
    simp
  exact UpperTheory.DirectSumIndependence.chase hyp.2.2.2.2.2.2.1 q i D
    (UpperTheory.DirectSumIndependence.Dp φ D (fun j => t.app j) ht)
    (UpperTheory.DirectSumIndependence.toDp φ D (fun j => t.app j) ht) (Cocone.mk C s) hs
    (UpperTheory.DirectSumIndependence.cocDp φ D (fun j => t.app j) ht (Cocone.mk C s) w φ' c
      (fun j => (hts j).2) hp)
    (UpperTheory.DirectSumIndependence.isColDp φ D (fun j => t.app j) ht (Cocone.mk C s) hs w φ' c
      (fun j => (hts j).2) hp)
    φ'
    (fun j => (UpperTheory.DirectSumIndependence.inr_coc φ D (fun j => t.app j) ht (Cocone.mk C s) w φ' c
      (fun j => (hts j).2) hp j).symm)
    (fun j => hEt _ _ (hts j).1 _ _ _ (IsPushout.of_hasPushout _ _))
    (fun j => UpperTheory.DirectSumIndependence.isUnit_of_hom (t.app j) hq)
