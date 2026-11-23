import Formalism.PeriodIntegrals.ThGDefs

namespace PI

def NormPullG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ (ψ : (T → I → J → ℂ) ≃ₗ[ℂ] (T → I → J → ℂ)), (∀ z w, HfG A (ψ z) (ψ w) = HfG A z w) →
    ∀ La₁ La₂ : AddSubgroup (T → I → J → ℂ), GoodLat s A La₁ → (∀ z, z ∈ La₂ ↔ ψ z ∈ La₁) →
      ∀ F ∈ ThSpG s A La₁, (fun z => F (ψ z)) ∈ ThSpG s A La₂ ∧ normSqG A La₂ (fun z => F (ψ z)) = normSqG A La₁ F

end PI
