import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdSd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdTr

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sdNormDV_of {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (hA : AnnX X ψ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) : SdNormDV X ψ := by
  have c1 : SdFromAnn := SdW.sdFromAnn_holds
  intro v hv ι _
  refine c1 ψ v (dV v) hψ ?_ ?_ (hA hψ hs v) ι
  · exact X.B.I.cm.deg2
  · exact VolOrdW.dV_ne_zero (v := v)

theorem volOrdV_of {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hC : CondAll) : VolOrdV X u u' ψ := by
  intro hψ hs
  exact volOrd_body X u u' ψ (sdNormDV_of X ψ (annX_of X ψ hC) hψ hs) SdW.boxScaleL_holds

end Formalism.L2.SG.Pf.NcVal
