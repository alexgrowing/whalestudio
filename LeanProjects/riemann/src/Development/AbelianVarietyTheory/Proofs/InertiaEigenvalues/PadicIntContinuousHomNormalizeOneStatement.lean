import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntContinuousHomNormalizeOne
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_continuous_hom_normalize_one : ∀ {G : Type} [Group G] [TopologicalSpace G] (p : ℕ) [Fact p.Prime] (χ : G → ℤ_[p]), Continuous χ → (∀ g h, χ (g * h) = χ g + χ h) → ∀ (g₀ : G), χ g₀ ≠ 0 → ∃ ψ : G → ℤ_[p], Continuous ψ ∧ (∀ g h, ψ (g * h) = ψ g + ψ h) ∧ (∀ g, χ g = 0 → ψ g = 0) ∧ ∃ g, ψ g = 1 := by
  first | exact @GlobalTheory.padicInt_hom_normalize | exact GlobalTheory.padicInt_hom_normalize | (intros; apply GlobalTheory.padicInt_hom_normalize <;> assumption)
