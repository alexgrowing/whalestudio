import Development.EtaleCohomology.EtaleSheaves.DescIntPf
import Development.EtaleCohomology.TateTwists.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescIntPf

namespace LateralTheory.E.CechSqPf

abbrev Ψ : CommRingCat.{0} ⥤ PShᵒᵖ := (Scheme.Spec ⋙ yoneda).rightOp

instance (n : ℕ) : PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ :=
  preservesColimitsOfShape_rightOp _ _

abbrev Sg {C D : CommRingCat.{0}} (g : C ⟶ D) : Spc := ((Arrow.mk g).cechConerve ⋙ Ψ).leftOp

abbrev ag {C D : CommRingCat.{0}} (g : C ⟶ D) : Sg g ⟶ sch.obj (Spec C) := lev Ψ (coAug g)

def sqHom {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') : Arrow.mk g ⟶ Arrow.mk (pushout.inr g φ') :=
  Arrow.homMk (u := φ') (v := pushout.inl g φ') pushout.condition.symm

theorem eqv_comp (R : Type) [CommRing R] (F : Shv R) {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'')
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := fun n => by
  have : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = (pull R f F n) ∘ (pull R g F n) := by
    funext x; exact pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

def IntegralSurjectiveRingCechAugmentationEtaleEqv : Prop := B4 → ∀ (q : ℕ) (i : ℤ) {C D : CommRingCat.{0}} (g : C ⟶ D), g.hom.IsIntegral → SpS g →
  IsUnit (q : C) → Eqv _ (cechAug (Spec.map g)) (tw q i)

def BaseChange : Prop := ∀ {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y'), g.hom.IsIntegral → SpS g →
  (pushout.inr g φ').hom.IsIntegral ∧ SpS (pushout.inr g φ')

def LevelPush : Prop := ∀ {A Y C D Y' : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) (w : Y ⟶ Y') (φ' : C ⟶ Y')
  (g : C ⟶ D), IsPushout φ c w φ' → ∀ n : SimplexCategory,
  IsPushout φ (c ≫ (coAug g).app n) (w ≫ (coAug (pushout.inr g φ')).app n) ((Arrow.mapCechConerve (sqHom g φ')).app n)

def LevelP : Prop := ∀ {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop), PushClosed P →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → ∀ n : SimplexCategory,
  P _ (c ≫ (coAug g).app n)

def Level0 : Prop := ∀ (q : ℕ) (i : ℤ) {A Y C D Y' : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) (w : Y ⟶ Y')
  (φ' : C ⟶ Y') (g : C ⟶ D), IsPushout φ c w φ' →
  ∃ (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : D ⟶ Z), IsPushout φ (c ≫ g) wz ψ ∧
    ∀ m, RelZ q i m ψ → RelZ q i m ((Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0))

theorem ag_eqv (q : ℕ) (i : ℤ) {C D : CommRingCat.{0}} (g : C ⟶ D)
    (h : Eqv _ (cechAug (Spec.map g)) (tw q i)) : Eqv _ (ag g) (tw q i) := by
  obtain ⟨e, he⟩ := LateralTheory.EtaleFoundations.etale_cech_conerve_image_iso_cech_nerve_of_preserves_wide_pushouts CommRingCat.{0} Ψ (fun n => inferInstance) C D g
  have h1 : (ag g) = e.hom ≫ cechAug (Spec.map g) := he
  rw [h1]
  exact eqv_comp _ _ _ _ (eqv_of_iso _ _ e) h

abbrev uMap {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') : Sg (pushout.inr g φ') ⟶ Sg g :=
  NatTrans.leftOp (Functor.whiskerRight (Arrow.mapCechConerve (sqHom g φ')) Ψ)

theorem u_sq {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') :
    uMap g φ' ≫ ag g = ag (pushout.inr g φ') ≫ sch.map (Spec.map φ') := by
  refine NatTrans.ext (funext fun n => ?_)
  have key : (coAug g).app n.unop ≫ (Arrow.mapCechConerve (sqHom g φ')).app n.unop =
      φ' ≫ (coAug (pushout.inr g φ')).app n.unop := by
    simp [coAug, sqHom]
    apply WidePushout.head_desc
  change (Ψ.map ((Arrow.mapCechConerve (sqHom g φ')).app n.unop)).unop ≫ (Ψ.map ((coAug g).app n.unop)).unop =
    (Ψ.map ((coAug (pushout.inr g φ')).app n.unop)).unop ≫ (Ψ.map φ').unop
  rw [← unop_comp, ← unop_comp, ← Ψ.map_comp, ← Ψ.map_comp, key]

theorem CechSq_of (h1 : IntegralSurjectiveRingCechAugmentationEtaleEqv) (h2 : BaseChange) (h3 : LevelPush) (h4 : LevelP) (h5 : Level0) : CechSq := by
  intro hH q _ i A Y φ hq P hP C D c g hCc hDc hgi hgs Y' w φ' hpo
  have hB4 : B4 := hH.2.2.2.2.2.2.2.2.1
  obtain ⟨hgi', hgs'⟩ := h2 g φ' hgi hgs
  have hqC : IsUnit (q : C) := by simpa using hq.map c.hom
  have hqY : IsUnit (q : Y') := by simpa using hqC.map φ'.hom
  refine ⟨_, _, uMap g φ', ag (pushout.inr g φ'), ag g, u_sq g φ', ag_eqv q i g (h1 hB4 q i g hgi hgs hqC),
    ag_eqv q i _ (h1 hB4 q i _ hgi' hgs' hqY), fun p => ?_, ?_⟩
  · exact ⟨_, c ≫ (coAug g).app (SimplexCategory.mk p), _, w ≫ (coAug (pushout.inr g φ')).app (SimplexCategory.mk p),
      _, h4 P hP c g hCc hDc _, h3 φ c w φ' g hpo _, fun m hm => hm⟩
  · obtain ⟨Z, wz, ψ, hpo0, hrel⟩ := h5 q i φ c w φ' g hpo
    exact ⟨Z, wz, ψ, hpo0, fun m hm => hrel m hm⟩

end LateralTheory.E.CechSqPf
