import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineCountOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfCountAtOf
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open GlobalTheory.SumCount GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosine_count_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.SumCount.CosK := by
  first | exact @GlobalTheory.CosCount.cosK | exact GlobalTheory.CosCount.cosK | (intros; apply GlobalTheory.CosCount.cosK <;> assumption)
