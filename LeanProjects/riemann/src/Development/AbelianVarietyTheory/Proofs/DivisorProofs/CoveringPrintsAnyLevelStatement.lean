import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringHypAnyLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anyLevSt_of_covering : GlobalTheory.CovTop.Hypotheses2 → AnyLevSt := by
  first | exact @GlobalTheory.DetHT.AnyLev.anyLev | exact GlobalTheory.DetHT.AnyLev.anyLev | (intros; apply GlobalTheory.DetHT.AnyLev.anyLev <;> assumption)
