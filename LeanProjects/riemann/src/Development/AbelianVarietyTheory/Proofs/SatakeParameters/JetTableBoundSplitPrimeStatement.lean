import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundSplitPrime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetTableBound_splitPrime : GlobalTheory.AtG.JetSplitAmb := by
  first | exact @GlobalTheory.AtG.jetSplitAmb_holds | exact GlobalTheory.AtG.jetSplitAmb_holds | (intros; apply GlobalTheory.AtG.jetSplitAmb_holds <;> assumption)
