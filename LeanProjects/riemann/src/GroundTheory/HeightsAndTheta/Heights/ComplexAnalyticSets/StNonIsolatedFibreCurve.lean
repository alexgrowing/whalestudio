import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

def NonIsolatedFibreCurve.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ) (p : Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → p ∈ U → AccPt p (𝓟 {v | v ∈ U ∧ f v = f p}) →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → Fin k → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = p ∧
          Set.MapsTo γ (ball 0 r) {v | v ∈ U ∧ f v = f p}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
