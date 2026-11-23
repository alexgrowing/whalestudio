import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACut

namespace Formalism.L2.SG.LocalCountModules.LocCntUL

def LocCntUL : Prop :=
  Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, Formalism.L2.SG.LsDatumA.ModSideU M r n false)

end Formalism.L2.SG.LocalCountModules.LocCntUL
