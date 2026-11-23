import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACut

namespace Formalism.L2.SG.LocalCountModules.LocCntUG

def LocCntUG : Prop :=
  Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, Formalism.L2.SG.LsDatumA.ModSideU M r n true)

end Formalism.L2.SG.LocalCountModules.LocCntUG
