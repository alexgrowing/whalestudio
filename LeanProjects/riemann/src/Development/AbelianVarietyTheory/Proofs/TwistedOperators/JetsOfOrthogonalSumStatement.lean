import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetsOfOrthogonalSum
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jets_of_orthogonal_sum : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → StepJets := by
  first | exact @GlobalTheory.RowClaim.JetsAssembly.stepJets | exact GlobalTheory.RowClaim.JetsAssembly.stepJets | (intros; apply GlobalTheory.RowClaim.JetsAssembly.stepJets <;> assumption)
