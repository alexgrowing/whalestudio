import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocalCountZeroLocalHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocCntUL

namespace Formalism.L2.SG.LsDatumA

theorem modSide0L : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n false) :=
  Formalism.L2.SG.LocalCountModules.localCountZeroLocal_holds

theorem modSideUL : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n false) :=
  Formalism.L2.SG.LocalCountModules.localCountUnitLocal_holds

end Formalism.L2.SG.LsDatumA
