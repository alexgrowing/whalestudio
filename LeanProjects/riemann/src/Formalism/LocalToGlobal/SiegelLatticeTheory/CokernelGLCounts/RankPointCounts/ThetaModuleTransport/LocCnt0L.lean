import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACut

namespace Formalism.L2.SG.LocalCountModules.LocCnt0L

def LocCnt0L : Prop :=
  Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, Formalism.L2.SG.LsDatumA.ModSide0 M r n false)

end Formalism.L2.SG.LocalCountModules.LocCnt0L
