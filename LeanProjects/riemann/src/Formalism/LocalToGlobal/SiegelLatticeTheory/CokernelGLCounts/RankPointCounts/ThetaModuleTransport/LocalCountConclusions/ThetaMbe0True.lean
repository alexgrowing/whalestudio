import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaMbe0GOfSplit
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.StepSplitHolds

namespace Formalism.L2.SG.LocalCountModules

open ValuativeRel in
theorem thetaMbe0_true {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E) (r n : ℕ) : Formalism.L2.SG.LocalCountModules.LocCntCommon.ThetaMbe0 M r n true :=
  Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.thetaMbe0G_of_split Formalism.L2.SG.LocalCountModules.AlgGSplit.stepSplit_holds M r n

end Formalism.L2.SG.LocalCountModules
