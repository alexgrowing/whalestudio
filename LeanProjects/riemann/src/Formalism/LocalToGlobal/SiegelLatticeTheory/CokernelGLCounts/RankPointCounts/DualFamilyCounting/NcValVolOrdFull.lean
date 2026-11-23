import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrd
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllPf

namespace Formalism.L2.SG.Pf.NcVal

theorem volOrdV_holds {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : VolOrdV X u u' ψ :=
  volOrdV_of X u u' ψ Formalism.L2.SG.Pf.conductor_inverse_different

end Formalism.L2.SG.Pf.NcVal
