import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontal_holds : HorizSt := by
  first | exact @GlobalTheory.HorizProof.horizSt | exact GlobalTheory.HorizProof.horizSt | (intros; apply GlobalTheory.HorizProof.horizSt <;> assumption)
