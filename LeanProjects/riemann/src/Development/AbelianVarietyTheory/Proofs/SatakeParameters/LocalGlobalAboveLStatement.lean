import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_above_l : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.Published.CaraianiLocalGlobal → GlobalTheory.Published.LocalGlobalAboveL := by
  first | exact @GlobalTheory.CaraianiAboveL.main | exact GlobalTheory.CaraianiAboveL.main | (intros; apply GlobalTheory.CaraianiAboveL.main <;> assumption)
