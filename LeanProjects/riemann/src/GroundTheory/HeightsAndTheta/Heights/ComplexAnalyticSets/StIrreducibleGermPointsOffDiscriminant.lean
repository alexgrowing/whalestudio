import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleFiniteGermProjectionOpenAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermPointsOffDiscriminant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x → GermIrreducibleAt X x →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A x), h y = 0) →
    ∃ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A x) ∧ (¬ ∀ᶠ y in 𝓝 (A x), δ y = 0) ∧
      ∀ W ∈ 𝓝 x, ∀ᶠ y in 𝓝 (A x), δ y ≠ 0 → ∃ x' ∈ X ∩ W, A x' = y

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
