import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RefinementHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refinement_holds : RefineSt := by
  first | exact @GlobalTheory.TorRef.refineSt | exact GlobalTheory.TorRef.refineSt | (intros; apply GlobalTheory.TorRef.refineSt <;> assumption)
