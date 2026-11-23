import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoBinomialRatioBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_binomial_ratio_bounds : ∀ T n : ℕ, 2 ≤ n → 11 * n ^ 2 ≤ T → (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n ∧ (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) := by
  first | exact @GlobalTheory.BinomRatio.two_binom_ratios | exact GlobalTheory.BinomRatio.two_binom_ratios | (intros; apply GlobalTheory.BinomRatio.two_binom_ratios <;> assumption)
