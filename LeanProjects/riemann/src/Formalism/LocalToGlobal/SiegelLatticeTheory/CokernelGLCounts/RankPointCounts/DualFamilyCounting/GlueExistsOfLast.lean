import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfLastDual
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FamilyDualHolds

namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_of_last (hL : Formalism.L2.SG.Pf.GluingBases.LastUnit) : GlueExists :=
  glueExists_of_last_dual hL Formalism.L2.SG.Pf.GluingBases.family_dual_holds

end Formalism.L2.SG.Pf.Cnt
