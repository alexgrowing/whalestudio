import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldIntegralFundamentalDomain
import Mathlib
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_setIntegral_tsum_of_fundamentalDomain : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G), μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → ∀ c g : G → ℂ, Integrable c μ → Continuous g → (∃ B : ℝ, ∀ w, ‖g w‖ ≤ B) → ∫ w, c w * g w ∂μ = ∫ w in 𝓕, ∑' γ : Γ, c ((γ : G) + w) * g ((γ : G) + w) ∂μ := by
  first | exact @GlobalTheory.unfold_integral_fundamentalDomain | exact GlobalTheory.unfold_integral_fundamentalDomain | (intros; apply GlobalTheory.unfold_integral_fundamentalDomain <;> assumption)
