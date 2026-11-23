import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.Partial
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.ThetaMbeUFalseOfAlg

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL

theorem locCntUL_of_alg (h : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.AlgAll) : Formalism.L2.SG.LocalCountModules.LocCntUL.LocCntUL :=
  locCntUL_of' (fun _ _ _ _ _ _ _ _ _ M _ r n => Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.thetaMbeU_false_of_alg h M r n)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL
