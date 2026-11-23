import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

noncomputable section

def ParametricCircleIntegralAnalytic.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Φ : (ι → ℂ) × ℂ → ℂ) (O : Set ((ι → ℂ) × ℂ)) (U : Set (ι → ℂ)) (c : ℂ) (r : ℝ),
    0 ≤ r → IsOpen O → IsOpen U → DifferentiableOn ℂ Φ O →
    (∀ x ∈ U, ∀ s ∈ sphere c r, (x, s) ∈ O) →
    AnalyticOnNhd ℂ (fun x => ∮ s in C(c, r), Φ (x, s)) U

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
