import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCnt0L
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ModularBoundZeroHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.CoordLHolds

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LWork

theorem locCnt0L_of
    (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbe0 M r n false))
    (h2 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r, Mbe0 M r)) :
    Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L := by
  intro F _ _ _ E _ _ _ _ M hOK r n hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂
  have hs : M.split = none := by simpa using hmode
  rw [h1 F E M hOK r n hmode V H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂]
  refine h2 F E M hOK r Z₁ Z₂ ?_ ?_
  · have : Z₁.Z.map M.R.subtype = H.Zhat t₁.f t₁.f' := by
      rw [e₁]; exact zzplusOf_none hs _ _ _
    unfold headDet; rw [this, ← dl_eq_det]; exact hD
  · have : Z₂.Z.map M.R.subtype = H.Zhat f₂ f₂' := by
      rw [e₂]; exact zzplusOf_none hs _ _ _
    unfold headDet; rw [this, ← dl_eq_det]; exact dl_zero_two hyp hD

theorem locCnt0L_of_theta
    (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbe0 M r n false)) :
    Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of h1 (fun _ _ _ _ _ _ _ _ _ M _ r => modularBoundZero_holds M r)

theorem locCnt0L_of_coordL_unramified (h1 : CoordL) (h2 : UnramifiedIsoCountZero) : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of_theta (thetaMbe0_L_of h1 h2)

theorem locCnt0L_of_alg (h2 : UnramifiedIsoCountZero) : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of_coordL_unramified coordL_holds h2

end Formalism.L2.SG.LocalCountModules.LocCnt0LWork
