import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def RegularLocusIdentity.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)), I.IsPrime →
    ∃ h : MvPolynomial σ ℂ, h ∉ I ∧ ∀ z ∈ zeroSetIn I, eval z h ≠ 0 → ∀ W ∈ 𝓝 z,
      ∃ V : Set (σ → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
        ∀ F : (σ → ℂ) → ℂ, AnalyticOnNhd ℂ F V →
          (∃ y ∈ zeroSetIn I ∩ V, ∀ᶠ u in 𝓝 y, u ∈ zeroSetIn I → F u = 0) →
            ∀ u ∈ zeroSetIn I ∩ V, F u = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
