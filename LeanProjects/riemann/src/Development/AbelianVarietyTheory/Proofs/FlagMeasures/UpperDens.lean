import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.HaarDensChart

def upperDens {V : Type} [PseudoMetricSpace V] [MeasurableSpace V] (l ν : Measure V) (x : V) : ℝ≥0∞ :=
  limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0)

end GlobalTheory.HaarDensChart
