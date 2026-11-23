import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylHighestWeightRestrictionBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_highest_weight_restriction_blockDiagonal : GlobalTheory.LeviCut.ResHw := by
  first | exact @GlobalTheory.LeviCut.resHw_holds | exact GlobalTheory.LeviCut.resHw_holds | (intros; apply GlobalTheory.LeviCut.resHw_holds <;> assumption)
