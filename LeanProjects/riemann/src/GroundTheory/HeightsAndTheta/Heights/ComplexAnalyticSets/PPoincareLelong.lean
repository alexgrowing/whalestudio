import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem PoincareLelong.proof (hStokes : StokesOnVariety.Statement)
    (hReg : LelongRegularise.Statement) (hLim : LelongLimit.Statement) :
    PoincareLelong.Statement := by
  intro n d J u f φ hJ hdim hu hf hfc hφ
  have hS : ∀ ε ∈ Set.Ioi (0 : ℝ), varInt J (d + 1) f (vecCons (logReg u ε) φ) =
      varInt J (d + 1) (logReg u ε) (vecCons f φ) := fun ε hε =>
    hStokes n d J f (logReg u ε) φ hJ hdim (smoothNear_of_contDiff hf)
      (smoothNear_of_contDiff (contDiff_logReg u hε)) hφ (Or.inl hfc)
  exact tendsto_nhds_unique (hReg n d J u f φ hJ hdim hu hf hfc hφ)
    ((hLim n d J u f φ hJ hdim hu hf hfc hφ).congr' (eventually_nhdsWithin_of_forall hS))

end GroundTheory.Heights₂.Heights
