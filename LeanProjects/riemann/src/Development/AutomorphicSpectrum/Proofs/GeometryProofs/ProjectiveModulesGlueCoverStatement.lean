import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModulesGlueCover

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_modules_glue_cover : ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : J → Type) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module (Localization.Away (f i)) (F i)]
    [∀ i, IsScalarTower R (Localization.Away (f i)) (F i)] [∀ i, Module.Finite (Localization.Away (f i)) (F i)]
    [∀ i, Module.Projective (Localization.Away (f i)) (F i)] (φ : ∀ i, E →ₗ[R] F i),
    (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (φ i)) → Module.Finite R E ∧ Module.Projective R E := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover | exact GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover | (intros; apply GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover <;> assumption)
