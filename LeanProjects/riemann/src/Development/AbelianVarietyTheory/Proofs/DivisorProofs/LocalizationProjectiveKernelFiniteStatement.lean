import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationProjectiveKernelFinite
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_projective_kernel_finite : ∀ (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M],
  Module.Projective (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) →
  ∀ (n : ℕ) (π : (Fin n → A) →ₗ[A] M), Function.Surjective π →
  Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) (LinearMap.ker π)) := by
  first | exact @GlobalTheory.finite_localized_ker_of_projective_away | exact GlobalTheory.finite_localized_ker_of_projective_away | (intros; apply GlobalTheory.finite_localized_ker_of_projective_away <;> assumption)
