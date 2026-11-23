import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem mk₁_comp_functor {C D : Type} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) {T T' : C} (φ : T ⟶ T') :
    (ComposableArrows.mk₁ φ ⋙ G : ComposableArrows D 1) = ComposableArrows.mk₁ (G.map φ) :=
  ComposableArrows.ext₁ rfl rfl (by show G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _; simp)

theorem mk₂_comp_functor {C D : Type} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) {T T' T'' : C}
    (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (ComposableArrows.mk₂ φ ψ ⋙ G : ComposableArrows D 2) = ComposableArrows.mk₂ (G.map φ) (G.map ψ) :=
  ComposableArrows.ext₂ rfl rfl rfl (by show G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _; simp)
    (by show G.map ψ = 𝟙 _ ≫ G.map ψ ≫ 𝟙 _; simp)

theorem dictionary_pull : ∀ {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (F' : C' ⥤ CommAlgCat.{0} R) (m : CoefMap (RingHom.id R) F F') (u₁ : H1 F →ₗ[R] HH F 1) (u₁' : H1 F' →ₗ[R] HH F' 1) (u₂ : H2 F →ₗ[R] HH F 2) (u₂' : H2 F' →ₗ[R] HH F' 2), IsIdealValuedLiftSystemCocycle F u₁ → IsIdealValuedLiftSystemCocycle F' u₁' → IsDegreeTwoComparison F u₂ → IsDegreeTwoComparison F' u₂' → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) → (∀ c, u₁' (m.pull1 c) = pullH m 1 (u₁ c)) ∧ (∀ c, u₂' (m.pull2 c) = pullH m 2 (u₂ c)) := by
  intro R _ C C' _ _ F F' m u₁ u₁' u₂ u₂' h1 h1' h2 h2' e1 e2
  refine ⟨fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    obtain ⟨x, hx⟩ := e1 f
    rw [h1 f x hx, pullH_mk, CoefMap.pullCohomologyOne_class]
    refine h1' _ _ fun T T' φ ↦ ?_
    have e : x.1 (ComposableArrows.mk₁ φ ⋙ m.G) = x.1 (ComposableArrows.mk₁ (m.G.map φ)) :=
      eq_of_heq (congr_arg_heq x.1 (mk₁_comp_functor m.G φ))
    exact (congrArg (m.α T') (e.trans (hx _ _ _)))
  · obtain ⟨f, rfl⟩ := H2.mk_surjective F c
    obtain ⟨x, hx⟩ := e2 f
    rw [h2 f x hx, pullH_mk, CoefMap.pullCohomologyTwo_class]
    refine h2' _ _ fun T T' T'' φ ψ ↦ ?_
    have e : x.1 (ComposableArrows.mk₂ φ ψ ⋙ m.G) = x.1 (ComposableArrows.mk₂ (m.G.map φ) (m.G.map ψ)) :=
      eq_of_heq (congr_arg_heq x.1 (mk₂_comp_functor m.G φ ψ))
    exact (congrArg (m.α T'') (e.trans (hx _ _ _ _ _)))

end GlobalTheory.CompanionTheory.HopfC
