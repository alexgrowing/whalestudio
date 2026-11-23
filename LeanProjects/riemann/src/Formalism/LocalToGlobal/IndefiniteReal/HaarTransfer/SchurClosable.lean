import Mathlib

namespace Formalism.IndefR.Leaf

open Filter Topology

def SchurClosable : Prop :=
  ∀ (G H H' : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (π : G →* (H →L[ℂ] H)) (π' : G →* (H' →L[ℂ] H')),
    (∀ g x, ‖π g x‖ = ‖x‖) → (∀ g x, ‖π' g x‖ = ‖x‖) →
    (∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H) →
    ∀ (D : Submodule ℂ H) (A : D →ₗ[ℂ] H'), Dense (D : Set H) →
      (∀ g, ∀ x ∈ D, π g x ∈ D) →
      (∀ g (x : D) (hx : π g x ∈ D), A ⟨π g x, hx⟩ = π' g (A x)) →
      (∀ (u : ℕ → D) (y : H'), Tendsto (fun n => (u n : H)) atTop (𝓝 0) →
        Tendsto (fun n => A (u n)) atTop (𝓝 y) → y = 0) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : D, inner ℂ (A x) (A y) = (c : ℂ) * inner ℂ (x : H) (y : H)

end Formalism.IndefR.Leaf
