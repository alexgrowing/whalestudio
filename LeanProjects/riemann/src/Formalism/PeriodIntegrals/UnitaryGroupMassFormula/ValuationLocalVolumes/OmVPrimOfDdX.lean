import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.BaseLatticeLeSecondIsotropic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVOfOpen
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVSt

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVSD_holds : OmVSD X := omVSD_of X (omVSDBwd_holds X)

theorem omVPrim_of_dd (hD : OmVDdLoc X) : OmVPrim X u' :=
  omVPrim_of X u' (omVMem_of X u' (omVMemEF_of X u' hD)) (omVZPrim_holds X u')

theorem omV_of_dd (hD : OmVDdLoc X) (hScale : OmVScale X u' ψ) (hBad : OmVBadT X u' ψ) (hLocU : OmVLocU X ψ) :
    Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  omV_of_open X u' ψ (omVSDBwd_holds X) (omVMemEF_of X u' hD) (omVZPrim_holds X u') hScale hBad hLocU

theorem omVSD_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVSD X := omVSD_holds X

theorem omVPrim_of_ddX (hD : OmVDdLoc X) : Formalism.L2.SG.Pf.NcX.OmVSt.OmVPrim X u' := omVPrim_of_dd X u' hD

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
