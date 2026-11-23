import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularityOfDensity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularity_of_density : DensSt → ModSt := by
  first | exact @GlobalTheory.FlatModel.modSt_of_densSt | exact GlobalTheory.FlatModel.modSt_of_densSt | (intros; apply GlobalTheory.FlatModel.modSt_of_densSt <;> assumption)
