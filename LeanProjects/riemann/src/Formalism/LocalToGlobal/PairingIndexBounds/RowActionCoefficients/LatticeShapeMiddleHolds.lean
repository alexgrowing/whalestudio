import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.FinalOf
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.XShape
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.BranchingSourceIdentity
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FrameEdgeIdentityHolds
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.TransposedFrameImageBlockwiseHolds
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.SubDRenameHvE
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.ProdItePow
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.SumIccEqRange

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

theorem lattice_shape_a_holds : XA := xA_of frame_shape_identity_holds
theorem lattice_span_normal_holds : XSpanN := xSpanN_of frame_shape_identity_holds
theorem lattice_shape_middle_holds : XMid := xMid_of frame_shape_identity_holds lattice_shape_a_holds frame_change_pairing_holds transposed_frame_image_blockwise_holds frame_change_compatibility_holds frame_change_group_action_holds
theorem lattice_shape_unit_holds : XUnit := xUnit_of frame_shape_identity_holds

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

theorem pending_tuple_admissible (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.FormalGroupSystem.adm7 D X (pendT X E hfin hst hLT pos F) :=
  pending_tuple_admissible_of_shape X E hfin hst hLT pos F frame_shape_identity_holds branching_source_identity branching_target_identity frame_change_injective_holds lattice_span_normal_holds lattice_shape_middle_holds lattice_shape_unit_holds
    frame_edge_identity_holds D

end Formalism.L2.PairingIndexBounds.Ent
