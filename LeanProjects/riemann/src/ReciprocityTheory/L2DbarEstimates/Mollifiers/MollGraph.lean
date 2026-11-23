import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollTendstoOfContinuous
import ReciprocityTheory.L2DbarEstimates.Mollifiers.FderivMollApply

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem moll_graph (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : GraphSt E μ ι := by
  intro l K hK m c v g w hw hg hw2
  refine ⟨fun k => moll_l2Tendsto E μ ι l K hK (g k) (hg k), ?_⟩
  refine (moll_l2Tendsto E μ ι l K hK w hw2).congr ?_
  intro i
  rw [moll_weakComm E μ m c v g w hw (K i)]

end ReciprocityTheory.L2DbarEstimates.B
