import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Development
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexAStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBBounded
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.InvMulMemOfScaledEntriesCongr
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.DeltaAE
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfCong
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.VolPinAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hyps_of {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (hPH : PrimeHyp D u (Tu D u')) :
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.Hyps D u u' (X.Fu u) (Y.what₂ u) := by
  refine ⟨PI.TCS.termStable_holds D u u', Formalism.L2.SG.Pf.term_equivalence_iff D u u', term_function_const D u u',
    hPH, D.sp.Y_sig 0, Y.rowsOK u⟩

theorem volIdxFinP (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (hPH : PrimeHyp D u (Tu D u')) :
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.VolumeIndexFiniteNonzero D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M := Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_finite_of_hyps D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M (hyps_of Y u u' hPH)
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.commens Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed (Formalism.L2.SG.Pf.StabilizerIndexVolumes.deltaAE_holds D _ _)
    (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_a_stable D u u' _ _ _ _) (Formalism.L2.SG.Pf.StabIntCong.aBddOf u u' _ _ _ _)
    (Formalism.L2.SG.Pf.StabIntCong.aCong u u' _ _ _ _) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_stable D u u' _ _ _ _)
    (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_bounded D u u' _ _ _ _) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_congruence D u u' _ _ _ _)

theorem volume_generic_odd_of_rep (hD : DictC) (hC : CovolOne3C) : Formalism.L2.SG.VolPin.VolumeOddGeneric := by
  refine volume_generic_odd_of hD hC (fun D X Y u u' hPH t w F' L U hrel hgen hNR hG => ?_)
    (fun D X Y u u' h => volIdxFinP D X Y u u' h)
  exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_stable D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed
    (hyps_of Y u u' hPH) Y.agree t.toTerm w F' L U hrel hgen hNR hG

end Formalism.L2.SG.Pf.VolPinAsm
