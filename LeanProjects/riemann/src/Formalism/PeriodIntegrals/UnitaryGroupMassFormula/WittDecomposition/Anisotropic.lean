import Mathlib
import Formalism.PeriodIntegrals.WittExtension

namespace PI.Witt

def OneVector : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K), (∀ x y, star (B x y) = B y x) →
    ∀ x y : V, B x x = B y y → B x x ≠ 0 →
      ∃ g : V ≃ₗ[K] V, (∀ z w, B (g z) (g w) = B z w) ∧ g x = y ∧
        ∀ z, B x z = 0 → B y z = 0 → g z = z

def Anisotropic : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K), (∀ x y, star (B x y) = B y x) →
    ∀ U : Submodule K V, (∃ x ∈ U, ∃ y ∈ U, B x y ≠ 0) → ∃ x ∈ U, B x x ≠ 0

end PI.Witt
