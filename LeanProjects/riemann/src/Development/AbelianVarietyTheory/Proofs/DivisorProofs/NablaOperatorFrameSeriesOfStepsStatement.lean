import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaOperatorFrameSeriesOfSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaOperatorFrameSeries_of_steps : InvDerSt → LinSt → FrameSt → NabSt := by
  first | exact @GlobalTheory.IsoTriv.nabSt_of | exact GlobalTheory.IsoTriv.nabSt_of | (intros; apply GlobalTheory.IsoTriv.nabSt_of <;> assumption)
