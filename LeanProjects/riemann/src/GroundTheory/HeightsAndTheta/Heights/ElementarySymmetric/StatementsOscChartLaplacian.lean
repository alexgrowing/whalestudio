import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.OscMuLineObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian MeasureTheory

namespace OscLine

def oscChartPot (x : ℂ) : ℝ :=
  Real.log (oscMuNorm (fun p => ![1, x] p.2))

end OscLine

def OscChartLaplacianNotIntegrable.Statement : Prop :=
  ∀ r : ℝ, 0 < r → ¬ IntegrableOn (fun x : ℂ => Δ OscLine.oscChartPot x) (Metric.ball (0 : ℂ) r)

end GroundTheory.Heights₂.Heights.LowerBoundFree
