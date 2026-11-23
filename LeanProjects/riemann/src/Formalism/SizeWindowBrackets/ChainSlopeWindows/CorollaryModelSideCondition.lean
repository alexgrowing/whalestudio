import Formalism.SizeWindowBrackets.SlopeExcessBoundExponentZero
import Formalism.SizeWindowBrackets.ChainSlopeWindows.WeightedMeanLemmaNeedsDegree
import Formalism.RankGapBounds.RankGapProofs.WeightedMeanData

open Real Filter

namespace Formalism.LFunctionChainParameters.PhiMonotonicityLemmas

theorem corollary_model_side_condition :
    (0 + 1 + ErrF (1 / 8) 1 32 (5 * (1 / 32) + 3 * (1 / 192)) (2 * (1 / 131072))) - 0 ≤ (32 : ℝ) := by
  have hs2 : Real.sqrt (2 * (1 / 131072)) = 1 / 256 := by
    rw [show (2 * (1 / 131072) : ℝ) = (1 / 256) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hl : Real.log (1 + 32 / 1) ≤ 6 * Real.log 2 := by
    rw [show (6 : ℝ) * Real.log 2 = Real.log (2 ^ 6) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h2 := Real.log_two_lt_d9
  unfold ErrF phi
  rw [hs2]
  norm_num at hl ⊢
  linarith

theorem corollary_final_model : CorFinalModel := by
  have hp : (2 : ℝ) ^ (5 : ℝ) = 32 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hn : (2 : ℝ) ^ (-(5 : ℝ)) = 1 / 32 := by
    rw [Real.rpow_neg (by norm_num), hp]; norm_num
  have hs1 : Real.sqrt (1 / 36864) = 1 / 192 := by
    rw [show (1 / 36864 : ℝ) = (1 / 192) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hs2 : Real.sqrt (2 * (1 / 131072)) = 1 / 256 := by
    rw [show (2 * (1 / 131072) : ℝ) = (1 / 256) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨0 + 1 + ErrF (1 / 8) 1 32 (5 * (1 / 32) + 3 * (1 / 192)) (2 * (1 / 131072)), 0, 1, 1 / 8,
    1, 1, 32, 5 * (1 / 32) + 3 * (1 / 192), 2 * (1 / 131072), 1 / 131072, 1 / 36864, 3, 1, 2, 5,
    le_refl _, by norm_num, by norm_num, by norm_num, ?_, by norm_num, le_refl _, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, rfl, by norm_num, ?_, by norm_num,
    corollary_model_side_condition, by ring⟩
  · rw [hp]; norm_num
  · rw [hn]; norm_num
  · rw [hn, hs1]
  · rw [hn, hs1, hs2]; norm_num

section SizeData₂

open Formalism.RankGapBounds.WeightedMeanData

end SizeData₂

end Formalism.LFunctionChainParameters.PhiMonotonicityLemmas
