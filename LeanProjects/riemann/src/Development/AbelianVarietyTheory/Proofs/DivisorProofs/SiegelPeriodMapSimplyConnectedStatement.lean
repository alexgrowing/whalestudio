import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnected
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_period_map_simply_connected : ∀ g : ℕ, IsPeriodMap (siegel g) tauU ∧ SimplyConnectedSpace (siegel g) := by
  first | exact @GlobalTheory.SiegelOpen.isPeriodMap_tauU_and_simplyConnected | exact GlobalTheory.SiegelOpen.isPeriodMap_tauU_and_simplyConnected | (intros; apply GlobalTheory.SiegelOpen.isPeriodMap_tauU_and_simplyConnected <;> assumption)
