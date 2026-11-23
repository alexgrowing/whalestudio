import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_statement_holds : DensSt := by
  first | exact @GlobalTheory.FlatModel.densSt | exact GlobalTheory.FlatModel.densSt | (intros; apply GlobalTheory.FlatModel.densSt <;> assumption)
