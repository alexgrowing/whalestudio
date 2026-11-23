import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVMemEFHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVScaleHoldsX
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfFfX
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertBHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LocalOmegaVolumeUnique
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmegaUnramifiedHolds

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVLocU_holds : OmVLocU X ψ := fun v a Y =>
  PI.OmLocU.Done.omLocU_closed X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) a Y

theorem omVBadT_holds : OmVBadT X u' ψ :=
  PI.OmVg.omVBadT_of_ff X u' ψ (OmW.omVStd_holds X ψ) (OmW.omVLat_holds X) (OmW.omVGram_holds X u')
    PI.OmVe.Top.fFInertB_holds PI.OmVe.Top.fFSplitB_holds

theorem omVBadT_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  PI.OmVg.omVBadT_of_ffX X u' ψ (Formalism.L2.SG.Pf.NcX.OmVSt.omega_standard_holds X ψ) (Formalism.L2.SG.Pf.NcX.OmVSt.omega_lattice_holds X)
    (OmW.omVGram_holds X u') PI.OmVe.Top.fFInertB_holds PI.OmVe.Top.fFSplitB_holds

theorem omV_holds : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  OmX.omV_of_rest X u' ψ (OmVc.omVScale_holds X u' ψ) (omVBadT_holds X u' ψ) (omVLocU_holds X ψ)

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVZGram : OmVGram X u' := Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.omVGram_holds X u'

theorem omVZDet : OmVDet X u' := Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.omVDet_holds X u'

theorem omVZLocU : OmVLocU X ψ := Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omVLocU_holds X ψ

theorem omVZ_holdsX : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  omV_of X u' ψ (omega_standard_holds X ψ) (omega_lattice_holds X) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.omVSD_holdsX X)
    (omega_unramified_holds X) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmX.omVPrim_holdsX X u') (omVZGram X u') (omVZDet X u')
    (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc.omVScale_holdsX X u' ψ) (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omVBadT_holdsX X u' ψ)
    (omVZLocU X ψ)

end Formalism.L2.SG.Pf.NcX.OmVSt

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem omV_holdsX {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  Formalism.L2.SG.Pf.NcX.OmVSt.omVZ_holdsX X u' ψ

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ
