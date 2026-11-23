import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageFiniteOfTrivialOnInfFiniteIndex
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_of_trivial_on_inf_finiteIndex : ∀ (G Q : Type) [Group G] [Group Q] (ρ : G →* Q) (J H : Subgroup G), H.FiniteIndex → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set G)).Finite := by
  first | exact @GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex | exact GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex | (intros; apply GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex <;> assumption)
