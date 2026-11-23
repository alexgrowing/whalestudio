import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobalCountOfSplitMode
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocalCountZeroGlobalHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocCntUG

namespace Formalism.L2.SG.LsDatumA

theorem modSide0G : ModSide0G := Formalism.L2.SG.LocalCountModules.localCountZeroGlobal_holds

theorem modSideUG : ModSideUG := Formalism.L2.SG.LocalCountModules.localCountUnitGlobal_holds

theorem integralClosureRank_and_residueTrdegLe (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.ThinScalesBound.T2 D := globalCount_of_split_mode D modSide0G modSideUG

end Formalism.L2.SG.LsDatumA
