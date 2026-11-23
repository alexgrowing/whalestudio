import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseLatticeConstructionHolds
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_lattice_construction_holds : GlobalTheory.TypeAsm.LatticeNormalizationCondition := by
  first | exact @GlobalTheory.TypeAsm.lat0C | exact GlobalTheory.TypeAsm.lat0C | (intros; apply GlobalTheory.TypeAsm.lat0C <;> assumption)
