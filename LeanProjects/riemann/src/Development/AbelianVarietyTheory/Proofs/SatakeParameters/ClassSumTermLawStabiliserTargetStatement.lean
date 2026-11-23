import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassSumTermLawStabiliserTarget
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_term_law_stabiliser_target : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → ∀ u μ (G : StabDat (D.chTw u μ)), StabPin t u μ G → ∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw (t.O u μ) i c c' g := by
  first | exact @GlobalTheory.KerJ.term_law | exact GlobalTheory.KerJ.term_law | (intros; apply GlobalTheory.KerJ.term_law <;> assumption)
