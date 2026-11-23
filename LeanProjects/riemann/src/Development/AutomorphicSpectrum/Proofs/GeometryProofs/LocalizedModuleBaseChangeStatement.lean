import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizedModuleBaseChange

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localized_module_base_change : ∀ (R P C C' : Type) [CommRing R] [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (f t : R) [AddCommGroup P] [Module R P]
  [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P] [Module.Finite (Localization.Away f) P]
  [Module.Projective (Localization.Away f) P], IsUnit (algebraMap R C f) → ∀ c : C →ₐ[R] C',
  IsLocalizedModule (Submonoid.powers t) c.toLinearMap →
  IsLocalizedModule (Submonoid.powers t) (LinearMap.compRight R c.toLinearMap : (P →ₗ[R] C) →ₗ[R] (P →ₗ[R] C')) := by
  first | exact @GlobalTheory.CompanionTheory.LocHom.isLocalizedModule_compRight_away | exact GlobalTheory.CompanionTheory.LocHom.isLocalizedModule_compRight_away | (intros; apply GlobalTheory.CompanionTheory.LocHom.isLocalizedModule_compRight_away <;> assumption)
