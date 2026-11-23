import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionStatementHolds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_reduction_statement_holds : GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.Statement := by
  first | exact @GlobalTheory.GradedLines.statement | exact GlobalTheory.GradedLines.statement | (intros; apply GlobalTheory.GradedLines.statement <;> assumption)
