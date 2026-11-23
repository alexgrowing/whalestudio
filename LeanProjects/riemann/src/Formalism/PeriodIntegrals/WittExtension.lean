import Mathlib

namespace PI

def WittExtension : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K), (∀ x y, star (B x y) = B y x) → (∀ x, (∀ y, B x y = 0) → x = 0) →
    ∀ (U : Submodule K V) (f : U →ₗ[K] V), Function.Injective f →
      (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ x : U, g x = f x

end PI
