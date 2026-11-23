import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ValNonneg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVLatHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVUnramHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.NegNatUnit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FrameVectorMemBaseLattice

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omV_of_open (hSDB : OmVSDBwd X) (hMem : OmVMemEF X u') (hZ : OmVZPrim X u')
    (hScale : OmVScale X u' ψ) (hBad : OmVBadT X u' ψ) (hLocU : OmVLocU X ψ) :
    Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  omV_of' X u' ψ (omVStd_holds X ψ) (omVLat_holds X) (omVSD_of X hSDB) (omVUnram_holds X)
    (omVPrim_of X u' (omVMem_of X u' hMem) hZ) (omVGram_holds X u') (omVDet_holds X u') hScale hBad hLocU

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
