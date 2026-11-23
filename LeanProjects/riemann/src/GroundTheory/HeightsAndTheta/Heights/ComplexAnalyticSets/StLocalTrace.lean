import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicOnSubset
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def LocalTrace.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ))
    (g : (σ → ℂ) → ℂ),
    I.IsPrime → w ∈ zeroSetIn I → U ∈ 𝓝 w → HolomorphicOnSubset g (zeroSetIn I ∩ U) →
    ∃ (k : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (B : Set (σ → ℂ)) (D : Set (Fin k → ℂ)) (m : ℕ)
      (T : (Fin k → ℂ) → ℂ),
      IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧ IsOpen D ∧ A w ∈ D ∧
      (∀ z ∈ zeroSetIn I ∩ B, A z = A w → z = w) ∧ DifferentiableOn ℂ T D ∧
      ∀ y ∈ D, ∃ x : Fin m → σ → ℂ, (∀ j, x j ∈ zeroSetIn I ∩ B ∧ A (x j) = y) ∧
        (∀ z ∈ zeroSetIn I ∩ B, A z = y → z ∈ Set.range x) ∧ T y = ∑ j, g (x j)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
