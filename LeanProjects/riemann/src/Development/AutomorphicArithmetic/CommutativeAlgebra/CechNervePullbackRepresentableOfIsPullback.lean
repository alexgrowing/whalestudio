import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.cechNerve_pullback_representable_of_isPullback :
    ∀ {Y X Y' X' Z Z' : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X') (b : X' ⟶ X) (m : cech f' ⟶ cech f), IsPullback m (cechAug f') (cechAug f) (sch.map b) → ∀ (k : SimplexCategoryᵒᵖ) (e : yoneda.obj Z ≅ (cech f).obj k) (g : Z ⟶ X) (c : Z' ⟶ Z) (g' : Z' ⟶ X'), e.hom ≫ (cechAug f).app k = yoneda.map g → IsPullback c g' g b → ∃ e' : yoneda.obj Z' ≅ (cech f').obj k, e'.hom ≫ m.app k = yoneda.map c ≫ e.hom := by
  intro Y X Y' X' Z Z' f f' b m hm k e g c g' he hc
  have h1 : IsPullback (m.app k) ((cechAug f').app k) ((cechAug f).app k) (yoneda.map b) :=
    hm.map ((evaluation _ _).obj k)
  have h2 : IsPullback (m.app k ≫ e.inv) ((cechAug f').app k) (yoneda.map g) (yoneda.map b) := by
    refine h1.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [← he]
      exact Category.comp_id _
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  have h3 : IsPullback (yoneda.map c) (yoneda.map g') (yoneda.map g) (yoneda.map b) :=
    hc.map yoneda
  refine ⟨IsPullback.isoIsPullback _ _ h3 h2, ?_⟩
  have h4 := IsPullback.isoIsPullback_hom_fst _ _ h3 h2
  calc (IsPullback.isoIsPullback _ _ h3 h2).hom ≫ m.app k
      = ((IsPullback.isoIsPullback _ _ h3 h2).hom ≫ (m.app k ≫ e.inv)) ≫ e.hom := by simp
    _ = yoneda.map c ≫ e.hom := by rw [h4]
