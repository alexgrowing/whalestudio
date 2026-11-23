import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGammaBound
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_gamma_bound : GlobalTheory.FunPr.Hypotheses₂ → FinGamK := by
  first | exact @GlobalTheory.GamLoss.finGamK | exact GlobalTheory.GamLoss.finGamK | (intros; apply GlobalTheory.GamLoss.finGamK <;> assumption)
