import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
import Mathlib
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ] (ν : Measure G) [ν.IsMulLeftInvariant] {𝓕 S : Set G}, IsFundamentalDomain Γ 𝓕 ν → MeasurableSet S → (∀ g, ∃ γ ∈ Γ, γ * g ∈ S) → ∀ {f : G → ℝ≥0∞}, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in S, f g ∂ν := by
  first | exact @GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits | exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits | (intros; apply GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits <;> assumption)
