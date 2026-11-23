import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectednessStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedness_statement_holds : GlobalTheory.CovTop.Hypotheses2 → ConnSt := by
  first | exact @GlobalTheory.FlatModel.connected_of_hypotheses | exact GlobalTheory.FlatModel.connected_of_hypotheses | (intros; apply GlobalTheory.FlatModel.connected_of_hypotheses <;> assumption)
