import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistenceOfComparison
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existence_of_comparison : CmpSt → ExSt := by
  first | exact @GlobalTheory.FlatModel.exSt_of_cmpSt | exact GlobalTheory.FlatModel.exSt_of_cmpSt | (intros; apply GlobalTheory.FlatModel.exSt_of_cmpSt <;> assumption)
