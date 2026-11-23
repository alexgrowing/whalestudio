import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlPtDCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlIntHolds

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

theorem NmlInv_holds : Formalism.L2.SG.NGCut.NormalInvariants.NmlInv :=
  nmlInv_of NmlLine_holds Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds NmlSep_holds

end Formalism.L2.SG.NGCut.NormalVectorPairings
