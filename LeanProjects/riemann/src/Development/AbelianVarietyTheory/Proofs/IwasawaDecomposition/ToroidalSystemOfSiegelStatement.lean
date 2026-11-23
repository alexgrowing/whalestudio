import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalSystemOfSiegel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_system_of_siegel : GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → SysExSt := by
  first | exact @GlobalTheory.TorRef.sysExSt_of_toroidal | exact GlobalTheory.TorRef.sysExSt_of_toroidal | (intros; apply GlobalTheory.TorRef.sysExSt_of_toroidal <;> assumption)
