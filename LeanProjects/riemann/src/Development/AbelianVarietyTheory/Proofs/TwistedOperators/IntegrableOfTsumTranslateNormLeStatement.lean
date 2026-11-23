import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfTsumTranslateNormLe
import Mathlib
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_of_tsum_norm_translate_le : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G), μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ c : G → ℂ, Continuous c → ∀ C : ℝ, (∀ w : G, Summable (fun γ : Γ => ‖c ((γ : G) + w)‖) ∧ ∑' γ : Γ, ‖c ((γ : G) + w)‖ ≤ C) → Integrable c μ := by
  first | exact @GlobalTheory.integrable_of_tsum_translate_norm_le | exact GlobalTheory.integrable_of_tsum_translate_norm_le | (intros; apply GlobalTheory.integrable_of_tsum_translate_norm_le <;> assumption)
