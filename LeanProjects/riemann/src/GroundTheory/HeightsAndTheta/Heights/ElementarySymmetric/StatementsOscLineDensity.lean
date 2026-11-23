import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsOscChartLaplacian
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian ReciprocityTheory.ChartRestriction.G.Geo

def OscLineDensity.Statement : Prop :=
  ∀ (A B : Fin 2 → ℂ) (y : Fin 1 → ℂ), A 0 * B 1 - A 1 * B 0 ≠ 0 → A 0 + B 0 * y 0 ≠ 0 →
    A 1 + B 1 * y 0 ≠ 0 →
    maDensity (fun _ y' => Real.log (OscLine.oscMuNorm (fun p => A p.2 + B p.2 * y' 0))) y =
      ‖A 0 * B 1 - A 1 * B 0‖ ^ 2 / (2 * Real.pi * ‖A 0 + B 0 * y 0‖ ^ 4) *
        Δ OscLine.oscChartPot ((A 1 + B 1 * y 0) / (A 0 + B 0 * y 0))

end GroundTheory.Heights₂.Heights.LowerBoundFree
