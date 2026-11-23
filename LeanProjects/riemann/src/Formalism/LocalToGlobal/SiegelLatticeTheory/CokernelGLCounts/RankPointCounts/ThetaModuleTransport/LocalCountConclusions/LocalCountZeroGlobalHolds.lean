import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.ThetaLocalCount.LocCnt0GOfTheta
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.ThetaMbe0True

namespace Formalism.L2.SG.LocalCountModules

theorem localCountZeroGlobal_holds : Formalism.L2.SG.LocalCountModules.LocCnt0G.LocCnt0G :=
  Formalism.L2.SG.LocalCountModules.LocCnt0GWork.locCnt0G_of_theta (by intro F _ _ _ E _ _ _ _ M _ r n; exact thetaMbe0_true M r n)

end Formalism.L2.SG.LocalCountModules
