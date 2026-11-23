import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NrmIdNonneg
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MtType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelBasisDeterminantAbsAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderTypeStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

namespace GlobalTheory.KerJ

theorem unUnit_of_mtType : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ u μ, MtType u (t.O u μ).mt) → t.ent.UnUnit := by
  intro D L hT Gi Gl K Y cX ex t hm u μ w hw i hi c c'
  have h3 := GlobalTheory.T.rhoThreeOf_of_determinantCharacterFiniteOrderType D u (D.chTw u μ) _ (hm u μ)
  have hb := CharVal.brRho_holds D _ _ h3
  rw [t.kf_un u μ w hw i hi c c']
  exact (t.kf u μ w hw).norm_un ((t.kf u μ w hw).unUnit_of t.idl t.idl_ok hb (GlobalTheory.T.kernelBasis_determinant_abs_at_place _ _ _ _ _ _ _ _ _)) hi c c'

end GlobalTheory.KerJ
