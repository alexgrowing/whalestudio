import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfBasis
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSplittingExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FamilyGramHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingVectorsExist
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LastRescaleOf

namespace Formalism.L2.SG.Pf.GluingBases

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueVecs_of_last (hL : LastUnit) : GlueVecs :=
  glueVecs_of gluing_vectors_exist (lastRescale_of hL)

end Formalism.L2.SG.Pf.GluingBases

namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_of_last_dual (hL : Formalism.L2.SG.Pf.GluingBases.LastUnit) (hD : Formalism.L2.SG.Pf.GluingBases.FamDual) :
    GlueExists :=
  glueExists_of_fam jordan_splitting_exists (Formalism.L2.SG.Pf.GluingBases.glueVecs_of_last hL)
    Formalism.L2.SG.Pf.GluingBases.family_top_holds Formalism.L2.SG.Pf.GluingBases.family_gram_holds hD

end Formalism.L2.SG.Pf.Cnt
