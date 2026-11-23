import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIntegralIndependent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartIndependent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartSplit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IntegralIndep.closed : IntegralIndep.Statement :=
  IntegralIndep.proof
    (PosPartIndep.proof
      (SheetOnlyNull.proof IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof
        IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof)
      PosPartLocal.proof PosPartSplit.proof)

end GroundTheory.Heights₂.Heights
