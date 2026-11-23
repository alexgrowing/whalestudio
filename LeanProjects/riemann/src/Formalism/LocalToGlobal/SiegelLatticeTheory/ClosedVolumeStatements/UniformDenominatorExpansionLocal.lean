import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProdExactHolds

namespace Formalism.L2.SG.Closed

theorem StepNormOne_holds : Formalism.L2.SG.NGCut.StepNormOne :=
  Formalism.L2.SG.NGCut.VanishingOrbitalPoints.stepNormOne_of_vanishLeaves AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds
    Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds

theorem StepPoints_holds : Formalism.L2.SG.NGCut.StepPoints :=
  Formalism.L2.SG.NGCut.VanishingOrbitalPoints.stepPoints_of_vanishLeaves AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds
    Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds

theorem ProdExact_holds : Formalism.L2.SG.Pf.NcReal.ProdExact := Formalism.L2.SG.RealObj.InfCut.ProductExactness.ProdExact_holds

end Formalism.L2.SG.Closed
