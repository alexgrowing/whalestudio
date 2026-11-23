import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_oneParameterLines_of_lieLines : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := by
  first | exact @GlobalTheory.RealLift.kLine_of_lineEx | exact GlobalTheory.RealLift.kLine_of_lineEx | (intros; apply GlobalTheory.RealLift.kLine_of_lineEx <;> assumption)
