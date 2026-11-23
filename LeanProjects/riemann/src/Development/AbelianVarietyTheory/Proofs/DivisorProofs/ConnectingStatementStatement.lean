import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ConnectingStatement : BridgeSt := by
  first | exact @GlobalTheory.DetHT.Bridge.bridge | exact GlobalTheory.DetHT.Bridge.bridge | (intros; apply GlobalTheory.DetHT.Bridge.bridge <;> assumption)
