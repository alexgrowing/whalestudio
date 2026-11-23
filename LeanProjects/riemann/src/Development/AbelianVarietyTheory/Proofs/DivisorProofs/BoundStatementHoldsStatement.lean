import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bound_statement_holds : BoundSt := by
  first | exact @GlobalTheory.FlatModel.boundSt | exact GlobalTheory.FlatModel.boundSt | (intros; apply GlobalTheory.FlatModel.boundSt <;> assumption)
