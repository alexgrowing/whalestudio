import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualModuleFiniteProjective

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_module_finite_projective : ∀ (R P : Type) [CommRing R] (f : R) [AddCommGroup P] [Module R P]
  [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P] [Module.Finite (Localization.Away f) P]
  [Module.Projective (Localization.Away f) P],
  Module.Finite (Localization.Away f) (P →ₗ[R] Localization.Away f) ∧ Module.Projective (Localization.Away f) (P →ₗ[R] Localization.Away f) := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.HomDual.finite_projective_hom | exact GlobalTheory.CompanionTheory.Ggeo.HomDual.finite_projective_hom | (intros; apply GlobalTheory.CompanionTheory.Ggeo.HomDual.finite_projective_hom <;> assumption)
