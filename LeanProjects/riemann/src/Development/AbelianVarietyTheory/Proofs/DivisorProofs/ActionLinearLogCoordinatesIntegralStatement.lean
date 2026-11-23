import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActionLinearLogCoordinatesIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.action_linear_logCoordinates_integral : ActSt := by
  first | exact @GlobalTheory.IsoTriv.actSt | exact GlobalTheory.IsoTriv.actSt | (intros; apply GlobalTheory.IsoTriv.actSt <;> assumption)
