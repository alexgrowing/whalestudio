import Mathlib

namespace PI

def WedgeDetNz : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (ρ : ℕ) (z : Fin ρ → V),
    LinearIndependent K z → ∃ φ : Fin ρ → (V →ₗ[K] K), (Matrix.of fun i k => φ i (z k)).det ≠ 0

end PI
