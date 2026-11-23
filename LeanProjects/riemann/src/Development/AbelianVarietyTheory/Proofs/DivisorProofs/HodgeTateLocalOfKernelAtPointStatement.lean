import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLocalOfKernelAtPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_local_of_kernel_at_point : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → HTLocSt := by
  first | exact @GlobalTheory.FlatModel.htLocSt_of_hodgeTateKernel | exact GlobalTheory.FlatModel.htLocSt_of_hodgeTateKernel | (intros; apply GlobalTheory.FlatModel.htLocSt_of_hodgeTateKernel <;> assumption)
