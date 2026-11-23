import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

def StatIdealStep : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A) (σ : A →+* A),
    (∀ r, σ r - r ∈ I) → (∀ r ∈ I, σ r - r ∈ I ^ 2) →
    ∀ (a : ℕ), ∀ r ∈ I ^ a, σ r - r ∈ I ^ (a + 1)

def StatFiltStep : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A) (σ : A →+* A) (N : Type) [AddCommGroup N] [Module A N]
    (γ : N →+ N), (∀ (r : A) (n : N), γ (r • n) = σ r • γ n) →
    (∀ (a : ℕ), ∀ r ∈ I ^ a, σ r - r ∈ I ^ (a + 1)) →
    (∀ n : N, γ n - n ∈ I • (⊤ : Submodule A N)) →
    ∀ (a : ℕ), ∀ x ∈ I ^ a • (⊤ : Submodule A N), γ x - x ∈ I ^ (a + 1) • (⊤ : Submodule A N)

def FrobeniusPowerCongruence : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ (A : Type) [CommRing A] (I : Ideal A) (σ : A →+* A) (N : Type)
    [AddCommGroup N] [Module A N] (γ : N →+ N), (∀ (r : A) (n : N), γ (r • n) = σ r • γ n) →
    (∀ r, σ r - r ∈ I) → (∀ r ∈ I, σ r - r ∈ I ^ 2) →
    (∀ n : N, γ n - n ∈ I • (⊤ : Submodule A N)) →
    ∀ b : ℕ, 1 ≤ b → ∀ x : N, ∃ y : N, ∃ z ∈ I ^ (ℓ ^ (b - 1)) • (⊤ : Submodule A N),
      (⇑γ)^[ℓ ^ b] x - x = (ℓ ^ 2) • y + z

def StatFreeK : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H1K H1m H0m H0KQ H0mQ H1mQ : Type)
    [AddCommGroup H1K] [Module ℤ_[ℓ] H1K] [AddCommGroup H1m] [Module ℤ_[ℓ] H1m]
    [AddCommGroup H0m] [Module ℤ_[ℓ] H0m] [AddCommGroup H0KQ] [Module ℤ_[ℓ] H0KQ]
    [AddCommGroup H0mQ] [Module ℤ_[ℓ] H0mQ] [AddCommGroup H1mQ] [Module ℤ_[ℓ] H1mQ]
    (res : H1K →ₗ[ℤ_[ℓ]] H1m) (cup : H0m →ₗ[ℤ_[ℓ]] H1m) (a0 : H0m →ₗ[ℤ_[ℓ]] H0mQ)
    (a1 : H1m →ₗ[ℤ_[ℓ]] H1mQ) (r0 : H0KQ →ₗ[ℤ_[ℓ]] H0mQ) (cupQ : H0mQ →ₗ[ℤ_[ℓ]] H1mQ) (al : ℕ),
    (∀ z, a1 (cup z) = cupQ (a0 z)) → Function.Injective cupQ →
    (∀ x : H1mQ, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) → FreeIn ℓ cup al →
    ∀ (y : H1K) (z : H0KQ), a1 (res y) = cupQ (r0 z) →
      ∃ zm : H0m, a0 zm = ((ℓ : ℤ_[ℓ]) ^ al) • r0 z

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
