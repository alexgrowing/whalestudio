import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoIntegralNormalisedPowPeak
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_integral_normalised_pow_smul_of_unique_peak : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X), IsProbabilityMeasure μ → ∀ (K : Set X) (x₀ : X) (f : X → ℝ), IsCompact K → μ Kᶜ = 0 → x₀ ∈ K → (∀ U : Set X, IsOpen U → x₀ ∈ U → 0 < μ U) → Continuous f → f x₀ = 1 → (∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) → (∀ U ∈ 𝓝 x₀, ∃ δ < 1, ∀ x ∈ K, x ∉ U → f x ≤ δ) → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : X → E), ContinuousOn F K → Tendsto (fun m : ℕ => ∫ x, ((f x ^ m / ∫ y, f y ^ m ∂μ : ℝ) : ℂ) • F x ∂μ) atTop (𝓝 (F x₀)) := by
  first | exact @GlobalTheory.tendsto_integral_normalised_pow_peak | exact GlobalTheory.tendsto_integral_normalised_pow_peak | (intros; apply GlobalTheory.tendsto_integral_normalised_pow_peak <;> assumption)
