import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormTwistedWeightLowerBound
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviForm_twisted_weight_lower_bound : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (z : M → V n) (φ ψ : M → ℝ) (δ : ℝ) (κ : ℝ → ℝ), IsLocalHomeomorph z → SmoothR n z φ → SmoothR n z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → ContDiff ℝ ∞ κ → (∀ t, t ≤ 0 → 0 ≤ deriv κ t ∧ deriv κ t ≤ 1) → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n z (fun x => φ x + α * ψ x)) → SmoothR n z (fun x => κ (δ * ψ x)) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n z (fun y => ((κ (δ * ψ y) : ℝ) : ℂ)) x ξ = ((deriv κ (δ * ψ x) * δ : ℝ) : ℂ) * dbarDot n z (fun y => (ψ y : ℂ)) x ξ ∧ deriv (deriv κ) (δ * ψ x) * (δ ^ 2 * ‖dbarDot n z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤ (Levi n z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := by
  first | exact @GlobalTheory.LeviTwistLower.main | exact GlobalTheory.LeviTwistLower.main | (intros; apply GlobalTheory.LeviTwistLower.main <;> assumption)
