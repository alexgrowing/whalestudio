import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseOfTateValueBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwise_of_tate_value_bound : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt → PtSt := by
  first | exact @GlobalTheory.FlatModel.ptSt_of_steps | exact GlobalTheory.FlatModel.ptSt_of_steps | (intros; apply GlobalTheory.FlatModel.ptSt_of_steps <;> assumption)
