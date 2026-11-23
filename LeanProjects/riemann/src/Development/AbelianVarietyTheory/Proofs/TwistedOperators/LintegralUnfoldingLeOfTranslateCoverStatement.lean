import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralUnfoldingLeOfTranslateCover
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_unfolding_le_of_translate_cover : ∀ (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H] (μ : Measure H) [μ.IsMulLeftInvariant] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G) [Countable Γ] (Kc : Set H), (∀ h, ∃ δ ∈ Γ.comap ι, δ * h ∈ Kc) → ∀ F : G → ENNReal, (∀ γ : G, Measurable fun h => F (γ * ι h)) → ∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, F ((q.out : Γ) * ι h) ∂μ ≤ ∫⁻ h in Kc, ∑' γ : Γ, F (γ * ι h) ∂μ := by
  first | exact @GlobalTheory.unfolding_cover_bound | exact GlobalTheory.unfolding_cover_bound | (intros; apply GlobalTheory.unfolding_cover_bound <;> assumption)
