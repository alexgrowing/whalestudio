import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjectiveVolume
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

def BergmanDensChartSum.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L) (dV : SmoothVolume A)
    (P : ChartPartition A) (g : X → ℝ), Continuous g →
      ∫ x, g x * bergmanDens W dV x ∂dV.μ =
        (∑ j, ∫ y in (A.chart j).target,
          P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * chernTopDens W j y) / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
