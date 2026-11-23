import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerBlockLastEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnGramDeterminant_unitLowerBlock_last_eq_one : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by
  first | exact @GlobalTheory.IntBall.colGramLast | exact GlobalTheory.IntBall.colGramLast | (intros; apply GlobalTheory.IntBall.colGramLast <;> assumption)
