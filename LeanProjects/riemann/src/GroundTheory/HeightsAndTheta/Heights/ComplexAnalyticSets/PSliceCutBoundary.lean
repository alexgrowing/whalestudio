import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutBoundary
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutDecay
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceCutBoundary.proof (hB : SliceBoundaryBound.Statement) (hD : SliceCutDecay.Statement) :
    SliceCutBoundary.Statement := by
  intro n e h W g ℓ A F G hW hg hℓ hA hF0 hG0 hF hG
  obtain ⟨C, hC0, hC⟩ := hB n e h W g ℓ A F G hW hg hℓ hA hF0 hG0 hF hG
  obtain ⟨D, hDk⟩ := hD n e h W g ℓ A hW hg hℓ hA
  have h1 : Tendsto (fun k : ℕ => D / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlim : Tendsto (fun k : ℕ => C * (D / ((k : ℝ) + 1) + Real.sqrt (D / ((k : ℝ) + 1)))) atTop
      (𝓝 0) := by
    simpa using (h1.add h1.sqrt).const_mul C
  refine squeeze_zero_norm (fun k => ?_) hlim
  rw [Real.norm_eq_abs]
  refine (hC _ (SliceCut.contDiff h k) (SliceCut.hasCompactSupport h k)).trans ?_
  obtain ⟨hm, he⟩ := hDk k
  gcongr

end GroundTheory.Heights₂.Heights
