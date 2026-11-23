import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FreeTraitHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_trait_holds : FreeTraitSt := by
  first | exact @GlobalTheory.TorRef.freeTrait | exact GlobalTheory.TorRef.freeTrait | (intros; apply GlobalTheory.TorRef.freeTrait <;> assumption)
