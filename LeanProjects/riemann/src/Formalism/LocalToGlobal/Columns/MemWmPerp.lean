import Mathlib

noncomputable section

namespace Formalism.L2.Col

variable {K : Type} [Field K] [StarRing K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def wmPerp (B : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule K V) : Submodule K V where
  carrier := {x | ∀ a ∈ A, B a x = 0}
  add_mem' := by
    intro x y hx hy a ha
    rw [map_add, hx a ha, hy a ha, add_zero]
  zero_mem' := by
    intro a _
    rw [map_zero]
  smul_mem' := by
    intro c x hx a ha
    rw [map_smul, hx a ha, smul_zero]

def wmZ (B : V →ₗ⋆[K] V →ₗ[K] K) (V₀ : Submodule K V) (θ : V →ₗ[K] W) : Submodule K V :=
  V₀ ⊓ wmPerp B (LinearMap.ker θ ⊓ V₀)

end Formalism.L2.Col
