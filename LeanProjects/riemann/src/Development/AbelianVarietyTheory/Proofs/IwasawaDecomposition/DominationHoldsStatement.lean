import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominationHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.domination_holds : DomSt := by
  first | exact @GlobalTheory.DomModels.domSt_holds | exact GlobalTheory.DomModels.domSt_holds | (intros; apply GlobalTheory.DomModels.domSt_holds <;> assumption)
