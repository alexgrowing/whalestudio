import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_statement_holds : ValueSt := by
  first | exact @GlobalTheory.FlatModel.valueSt | exact GlobalTheory.FlatModel.valueSt | (intros; apply GlobalTheory.FlatModel.valueSt <;> assumption)
