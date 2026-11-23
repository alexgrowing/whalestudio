import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormPeriodLowerBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitian
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_period_lower_bound : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E F : Fin g → Fin g → ℂ) (τ : Fin g → Fin g → ℂ) (c D Λ : ℝ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i j, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (E i) (E j)).im = 0) → (∀ i j, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (F i) (E j)).im = if i = j then 1 else 0) → 0 < c → (∀ v : Fin g → ℝ, c * ‖v‖ ^ 2 ≤ D * (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im) → ‖τ‖ ≤ Λ → ∀ a : Fin g → ℂ, c * ‖a‖ ^ 2 ≤ D * ((g : ℝ) * Λ) ^ 2 * (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (∑ k, a k • E k) (∑ k, a k • E k)).re ∧ c * (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (∑ k, a k • E k) (∑ k, a k • E k)).re ≤ 2 * (g : ℝ) ^ 2 * D * ‖a‖ ^ 2 := by
  first | exact @GlobalTheory.hermForm_isotropic_combination_norm_compare | exact GlobalTheory.hermForm_isotropic_combination_norm_compare | (intros; apply GlobalTheory.hermForm_isotropic_combination_norm_compare <;> assumption)
