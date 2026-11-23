import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingIntegralCosetRepresentatives
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_integral_coset_representatives : ∀ {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) [μ.IsMulLeftInvariant], (∀ g : G, Measurable (fun x => g * x)) →
    ∀ (Γ Q : Subgroup G), Countable Γ → Q ≤ Γ → ∀ (D₀ D : Set G), IsFundamentalDomain Γ D₀ μ → IsFundamentalDomain Q D μ →
    ∀ {ι : Type} [Countable ι] (γ : ι → G), (∀ i, γ i ∈ Γ) → (∀ δ ∈ Γ, ∃! i, δ * (γ i)⁻¹ ∈ Q) →
    ∀ f : G → ℂ, (∀ q ∈ Q, ∀ g, f (q * g) = f g) → IntegrableOn f D μ →
      ∫ g in D₀, ∑' i, f (γ i * g) ∂μ = ∫ g in D, f g ∂μ := by
  first | exact @GlobalTheory.integral_tsum_cosetReps_eq_integral_fundamentalDomain | exact GlobalTheory.integral_tsum_cosetReps_eq_integral_fundamentalDomain | (intros; apply GlobalTheory.integral_tsum_cosetReps_eq_integral_fundamentalDomain <;> assumption)
