import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricSeriesMultiIndex
import Mathlib
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_series_multi_index : ∀ {ι : Type} [Fintype ι] (a : ι → ℤ) (r : ι → ℂ), (∀ i, r i ≠ 0) → (∀ i, ‖r i‖ < 1) →
    Summable (fun k : ι → ℤ => ‖if (∀ i, a i ≤ k i) then ∏ i, r i ^ k i else 0‖) ∧
    ∑' k : ι → ℤ, (if (∀ i, a i ≤ k i) then ∏ i, r i ^ k i else 0) = ∏ i, r i ^ a i * (1 - r i)⁻¹ := by
  first | exact @GlobalTheory.tsum_prod_geom_zpow_ge | exact GlobalTheory.tsum_prod_geom_zpow_ge | (intros; apply GlobalTheory.tsum_prod_geom_zpow_ge <;> assumption)
