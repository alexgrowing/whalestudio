import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfLocallyFiniteFreeLocalizations
import Mathlib
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_locally_finite_free_localizations : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M], (∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F) (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F) (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ) → Module.Finite R M ∧ Module.Projective R M := by
  first | exact @GlobalTheory.LocFreeProj.finite_projective_of_locally_free | exact GlobalTheory.LocFreeProj.finite_projective_of_locally_free | (intros; apply GlobalTheory.LocFreeProj.finite_projective_of_locally_free <;> assumption)
