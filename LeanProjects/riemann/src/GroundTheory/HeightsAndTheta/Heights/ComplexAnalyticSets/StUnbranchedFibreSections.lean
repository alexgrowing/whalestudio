import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LocalParametrisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def UnbranchedFibreSections.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ),
    IsLocalParametrisation X w B A D δ N → ∀ y₀ ∈ D, δ y₀ ≠ 0 →
    ∃ (r : ℝ) (g : Fin N → (Fin d → ℂ) → σ → ℂ), 0 < r ∧ Metric.ball y₀ r ⊆ D ∧
      (∀ y ∈ Metric.ball y₀ r, δ y ≠ 0) ∧ (∀ i, AnalyticOnNhd ℂ (g i) (Metric.ball y₀ r)) ∧
      ∀ y ∈ Metric.ball y₀ r, Function.Injective (fun i => g i y) ∧
        {x | x ∈ X ∩ B ∧ A x = y} = Set.range (fun i => g i y)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
