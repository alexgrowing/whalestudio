import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_statement_holds : CmpSt := by
  first | exact @GlobalTheory.FlatModel.cmpSt_holds | exact GlobalTheory.FlatModel.cmpSt_holds | (intros; apply GlobalTheory.FlatModel.cmpSt_holds <;> assumption)
