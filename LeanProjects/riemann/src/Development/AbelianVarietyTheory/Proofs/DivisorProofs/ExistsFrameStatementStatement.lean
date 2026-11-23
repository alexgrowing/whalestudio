import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ExistsFrameStatement : ExFrameSt := by
  first | exact @GlobalTheory.DetHT.exFrameSt_holds | exact GlobalTheory.DetHT.exFrameSt_holds | (intros; apply GlobalTheory.DetHT.exFrameSt_holds <;> assumption)
