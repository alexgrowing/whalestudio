import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.SiegelWeilFormula.Act

theorem exch {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable ι] {μ : Measure α} {m : Measure β}
    [SFinite μ] [SFinite m] (g : ι → α × β → ℂ) (hi : ∀ i, Integrable (g i) (μ.prod m))
    (hs : Summable fun i => ∫ p, ‖g i p‖ ∂(μ.prod m)) :
    Summable (fun i => ∫ u, ∫ v, g i (u, v) ∂m ∂μ) ∧
      ∫ u, ∫ v, (∑' i, g i (u, v)) ∂m ∂μ = ∑' i, ∫ u, ∫ v, g i (u, v) ∂m ∂μ := by
  have hsum : HasSum (fun i => ∫ u, ∫ v, g i (u, v) ∂m ∂μ) (∫ p, ∑' i, g i p ∂(μ.prod m)) := by
    have h := hasSum_integral_of_summable_integral_norm hi hs
    rw [show (fun i => ∫ p, g i p ∂(μ.prod m)) = fun i => ∫ u, ∫ v, g i (u, v) ∂m ∂μ from
      funext fun i => integral_prod (g i) (hi i)] at h
    exact h
  have hint : Integrable (fun p => ∑' i, g i p) (μ.prod m) := by
    refine ⟨AEStronglyMeasurable.tsum fun i => (hi i).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ p, ‖∑' i, g i p‖ₑ ∂(μ.prod m) ≤ ∫⁻ p, ∑' i, ‖g i p‖ₑ ∂(μ.prod m) :=
          lintegral_mono fun p => enorm_tsum_le_tsum_enorm
      _ = ∑' i, ∫⁻ p, ‖g i p‖ₑ ∂(μ.prod m) :=
          lintegral_tsum fun i => (hi i).aestronglyMeasurable.enorm
      _ = ∑' i, ENNReal.ofReal (∫ p, ‖g i p‖ ∂(μ.prod m)) := by
          congr 1
          funext i
          rw [ofReal_integral_norm_eq_lintegral_enorm (hi i)]
      _ = ENNReal.ofReal (∑' i, ∫ p, ‖g i p‖ ∂(μ.prod m)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun p => norm_nonneg _) hs).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq, integral_prod _ hint]

end PositivityTheory.SiegelWeilFormula.Act

end
