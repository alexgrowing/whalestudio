import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeArcHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_arc_holds : ConeArcSt := by
  first | exact @GlobalTheory.ConeArc.coneArc | exact GlobalTheory.ConeArc.coneArc | (intros; apply GlobalTheory.ConeArc.coneArc <;> assumption)
