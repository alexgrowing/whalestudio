import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankFourLtTop
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankFour_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 3) → ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.Fin4.lintegral_hB_four_lt_top | exact GlobalTheory.IntBall.Fin4.lintegral_hB_four_lt_top | (intros; apply GlobalTheory.IntBall.Fin4.lintegral_hB_four_lt_top <;> assumption)
