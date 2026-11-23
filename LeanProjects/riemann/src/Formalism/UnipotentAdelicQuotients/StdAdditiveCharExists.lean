import Mathlib

namespace HeckeCharacterZeroLocus

open NumberField

def StdAdditiveCharExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F →
    ∃ ψ : AddChar (AdeleRing (𝓞 F) F) ℂ, Continuous ψ ∧ (∀ x, ‖ψ x‖ = 1) ∧
      (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) ∧ (∃ x, ψ x ≠ 1) ∧
      ∀ x : InfiniteAdeleRing F, ψ (x, 0) =
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ)))

end HeckeCharacterZeroLocus
