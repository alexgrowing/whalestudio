import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFanOfToroidalCharts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fan_of_toroidal_charts : GlobalTheory.Published.ToroidalChartsForFan → GenFanSt := by
  first | exact @GlobalTheory.GenFan.genFanSt_of_toroidalCharts | exact GlobalTheory.GenFan.genFanSt_of_toroidalCharts | (intros; apply GlobalTheory.GenFan.genFanSt_of_toroidalCharts <;> assumption)
