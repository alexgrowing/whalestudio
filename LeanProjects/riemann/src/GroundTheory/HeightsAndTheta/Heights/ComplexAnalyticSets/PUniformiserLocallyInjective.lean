import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserLocallyInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserGradientIndependent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolynomialChartInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem UniformiserLocallyInjective.proof (hgrad : UniformiserGradientIndependent.Statement)
    (hchart : PolynomialChartInjective.Statement) : UniformiserLocallyInjective.Statement := by
  intro σ _ I w t hI hic hdim hw ht
  obtain ⟨k, f, hk, hfI, hli⟩ := hgrad σ I w t hI hic hdim hw ht
  obtain ⟨U, hU, hinj⟩ := hchart σ k t f w hk hli
  refine ⟨U, hU, hinj.mono ?_⟩
  rintro z ⟨hz, hzU⟩
  exact ⟨hzU, fun j ↦ hz (f j) (hfI j)⟩

end GroundTheory.Heights₂.Heights
