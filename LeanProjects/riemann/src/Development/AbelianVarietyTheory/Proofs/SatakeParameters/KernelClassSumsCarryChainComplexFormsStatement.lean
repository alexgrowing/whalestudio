import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelClassSumsCarryChainComplexForms
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelClassSums_carry_chainComplexForms : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → FormsPin t → OrbitPlaces.KFi D ex.tw := by
  first | exact @GlobalTheory.KFiClose.kFi_of_tie | exact GlobalTheory.KFiClose.kFi_of_tie | (intros; apply GlobalTheory.KFiClose.kFi_of_tie <;> assumption)
