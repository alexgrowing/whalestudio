import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolomorphicOnSubset {σ : Type*} [Fintype σ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : (σ → ℂ) → E) (S : Set (σ → ℂ)) : Prop :=
  ∀ z ∈ S, ∃ U : Set (σ → ℂ), IsOpen U ∧ z ∈ U ∧ ∃ F : (σ → ℂ) → E,
    DifferentiableOn ℂ F U ∧ Set.EqOn f F (S ∩ U)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
