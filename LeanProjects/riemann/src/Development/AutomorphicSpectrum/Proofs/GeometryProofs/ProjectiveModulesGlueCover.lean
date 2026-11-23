import Mathlib

namespace GlobalTheory.CompanionTheory.Ggeo

theorem finite_projective_of_isLocalizedModule_cover :
    ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : J → Type) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module (Localization.Away (f i)) (F i)]
    [∀ i, IsScalarTower R (Localization.Away (f i)) (F i)] [∀ i, Module.Finite (Localization.Away (f i)) (F i)]
    [∀ i, Module.Projective (Localization.Away (f i)) (F i)] (φ : ∀ i, E →ₗ[R] F i),
    (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (φ i)) → Module.Finite R E ∧ Module.Projective R E := by
  intro R E _ _ _ J _ f hf F _ _ _ _ _ _ φ hφ
  have hex : ∀ g : Set.range f, ∃ i, f i = g.1 := fun g => g.2
  choose idx hidx using hex
  have hA : ∀ g : Set.range f, IsLocalization.Away g.1 (Localization.Away (f (idx g))) := by
    intro g
    rw [← hidx g]
    infer_instance
  have hL : ∀ g : Set.range f, IsLocalizedModule (Submonoid.powers g.1) (φ (idx g)) := by
    intro g
    rw [← hidx g]
    exact hφ _
  have hfp : Module.FinitePresentation R E :=
    Module.FinitePresentation.of_localizationSpan' (Set.range f) hf
      (Mₚ := fun g => F (idx g)) (Rₚ := fun g => Localization.Away (f (idx g)))
      (fun g => φ (idx g)) (fun g => Module.finitePresentation_of_projective _ _)
  have hflat : Module.Flat R E := by
    refine Module.flat_of_isLocalized_span (R := R) R E (Set.range f) hf (fun g => F (idx g))
      (fun g => φ (idx g)) (fun g => ?_)
    have : Module.Flat R (Localization.Away (f (idx g))) :=
      IsLocalization.flat _ (Submonoid.powers (f (idx g)))
    exact Module.Flat.trans R (Localization.Away (f (idx g))) (F (idx g))
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.CompanionTheory.Ggeo
