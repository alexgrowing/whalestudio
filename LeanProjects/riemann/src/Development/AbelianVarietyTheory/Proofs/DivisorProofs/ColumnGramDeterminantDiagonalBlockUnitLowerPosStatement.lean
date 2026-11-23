import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantDiagonalBlockUnitLowerPos
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos : ∀ (r p0 : ℕ) (w : Low r → ℂ) (k : Fin (r - 1 + 1)), 0 < colGram (blkW p0 w) k := by
  first | exact @GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos | exact GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos | (intros; apply GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos <;> assumption)
