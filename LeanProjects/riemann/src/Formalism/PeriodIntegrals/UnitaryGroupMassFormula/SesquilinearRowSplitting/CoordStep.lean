import Mathlib

open NumberField

namespace PI.SRW

def RepStep : Prop :=
  ∀ (E V : Type) [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E), h.Nondegenerate →
    ∀ (Λ : Submodule (𝓞 E) V), Submodule.IsLattice E Λ →
    ∀ ℓ : Λ →ₗ[𝓞 E] E, ∃ w : V, ∀ x : Λ, h w x = ℓ x

def CoordStep : Prop :=
  ∀ (E V : Type) [Field E] [AddCommGroup V] [Module E V] (n : ℕ) (g : Fin n → V),
    LinearIndependent E g → ∃ c : Fin n → (V →ₗ[E] E), ∀ i j, c i (g j) = if i = j then 1 else 0

def RetrStep : Prop :=
  ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (Λ N : Submodule (𝓞 E) V), N ≤ Λ → Λ.FG →
    (∀ (o : 𝓞 E) (x : V), o ≠ 0 → x ∈ Λ → o • x ∈ N → x ∈ N) →
    ∃ ρ : Λ →ₗ[𝓞 E] V, (∀ x : Λ, ρ x ∈ N) ∧ ∀ x : Λ, (x : V) ∈ N → ρ x = x

end PI.SRW
