import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogNormEnergyDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogNormGradDensNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LogNormEnergyDensNonneg.proof : LogNormEnergyDensNonneg.Statement := by
  intro n d h s y v hs hsy
  exact LogNormGradDensNonneg.proof n d h s y v hs hsy

end GroundTheory.Heights₂.Heights
