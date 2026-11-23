import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.LocCntULOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.CornerU

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL

theorem locCntUL_of'
    (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbeU M r n false)) : Formalism.L2.SG.LocalCountModules.LocCntUL.LocCntUL :=
  locCntUL_of h1 (fun _ _ _ _ _ _ _ _ _ M _ r => mbeU_holds M r)
    (fun _ _ _ _ _ _ _ _ _ M _ r => cornerU_holds M r)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL
