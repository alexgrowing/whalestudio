import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrableDensityOfBoundByIntegralCompactA
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integrable_density_of_bound_by_integral_on_compact : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (K : Set X), IsCompact K → μ K < ⊤ → ∀ (S : Submodule ℂ (X → ℂ)), (∀ f ∈ S, Continuous f) → ∀ (Λ : (X → ℂ) → ℂ) (C : ℝ), (∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ (c • f + f') = c * Λ f + Λ f') → (∀ f ∈ S, ‖Λ f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ) → ∃ a : X → ℂ, Measurable a ∧ Integrable a μ ∧ (∀ x ∉ K, a x = 0) ∧ ∀ f ∈ S, ∫ x, f x * a x ∂μ = Λ f := by
  first | exact @GlobalTheory.exists_integrable_density_of_bound_by_integral_compact | exact GlobalTheory.exists_integrable_density_of_bound_by_integral_compact | (intros; apply GlobalTheory.exists_integrable_density_of_bound_by_integral_compact <;> assumption)
