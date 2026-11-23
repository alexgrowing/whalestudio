import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetLeOfWeightedEntryBound
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_det_le_of_weighted_entry_bound : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u : Equiv.Perm (Fin n)) (w : Fin n → ℝ) (c : ℝ), (∀ a, 0 < w a) → (∀ i b, ‖M i b‖ * (w (u i) * w b) ≤ c) → ‖M.det‖ ≤ (n.factorial : ℝ) * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  first | exact @GlobalTheory.GoodTop.norm_det_le_of_weighted | exact GlobalTheory.GoodTop.norm_det_le_of_weighted | (intros; apply GlobalTheory.GoodTop.norm_det_le_of_weighted <;> assumption)
