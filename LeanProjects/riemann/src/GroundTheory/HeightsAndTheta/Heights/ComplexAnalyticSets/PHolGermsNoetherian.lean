import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsNoetherian
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermsNoetherian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem HolGermsNoetherian.proof (hN : AnalyticGermsNoetherian.Statement) : HolGermsNoetherian.Statement :=
  fun σ _ w => hN σ w

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
