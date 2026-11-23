import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingOfComparison
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifting_of_comparison : CmpSt → LiftSt := by
  first | exact @GlobalTheory.FlatModel.liftSt_of_cmpSt | exact GlobalTheory.FlatModel.liftSt_of_cmpSt | (intros; apply GlobalTheory.FlatModel.liftSt_of_cmpSt <;> assumption)
