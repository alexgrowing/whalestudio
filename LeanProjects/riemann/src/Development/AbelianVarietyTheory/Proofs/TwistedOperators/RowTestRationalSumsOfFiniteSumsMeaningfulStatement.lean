import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRationalSumsOfFiniteSumsMeaningful
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTestRationalSums_of_finiteSumsMeaningful : GlobalTheory.RowClaim.SumOKK → GlobalTheory.RowClaim.SumRatK := by
  first | exact @GlobalTheory.RowTest.sumRatK_of_sumOKK | exact GlobalTheory.RowTest.sumRatK_of_sumOKK | (intros; apply GlobalTheory.RowTest.sumRatK_of_sumOKK <;> assumption)
