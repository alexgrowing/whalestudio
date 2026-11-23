import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_holds : UniformSt := by
  first | exact @GlobalTheory.TorRef.Unif.uniformSt | exact GlobalTheory.TorRef.Unif.uniformSt | (intros; apply GlobalTheory.TorRef.Unif.uniformSt <;> assumption)
