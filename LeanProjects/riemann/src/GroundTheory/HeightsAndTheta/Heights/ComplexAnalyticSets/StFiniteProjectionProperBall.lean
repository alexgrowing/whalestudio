import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteProjectionProperBall.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ U ∈ 𝓝 w, ∃ ρ : ℝ, 0 < ρ ∧ ∃ r : ℝ, 0 < r ∧ Metric.ball w ρ ⊆ U ∧
      ∀ K ⊆ Metric.ball (A w) r, IsCompact K →
        IsCompact {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
