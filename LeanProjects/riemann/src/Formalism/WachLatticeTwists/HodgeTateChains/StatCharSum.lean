import Formalism.WachLatticeTwists.HodgeTateChains.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

def StatKappa : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ (s : ℕ) (ρ : ℚ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) → 0 < ρ → ρ < s →
    ∀ j : ℕ, 1 ≤ j → j ≤ ℓ ^ s → 0 < (s : ℚ) - padicValNat ℓ j + ((j : ℚ) - 2) * ρ

def StatNilDiv : Prop :=
  ∀ (La : Type) [CommRing La] (a b : La) (M q : ℕ), 1 ≤ M → (a - b) ^ M = 0 → a ^ q ∣ b ^ (q + M - 1)

def StatCharSum : Prop :=
  ∀ (R : Type) [CommRing R] (ℓ : ℕ) (ζ : ℕ → R), ζ 0 = 1 → (∀ i, ζ (i + 1) ^ ℓ = ζ i) →
    ∑ k ∈ Finset.range ℓ, ζ 1 ^ k = 0 →
    ∀ s j i n : ℕ, j ≤ s →
      (i ≤ j → ∑ k ∈ Finset.range (ℓ ^ (s - j)), ζ i ^ (n + ℓ ^ j * k) = (ℓ ^ (s - j)) • ζ i ^ n) ∧
      (j < i → i ≤ s → ∑ k ∈ Finset.range (ℓ ^ (s - j)), ζ i ^ (n + ℓ ^ j * k) = 0)

def StatRValues : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    ∀ (e : ℕ), 1 ≤ e → ∀ (abelian₂ : Type) [AddCommGroup abelian₂] [Module ℤ_[ℓ] abelian₂] (L : ℕ → Type)
      [∀ j, AddCommGroup (L j)] [∀ j, Module ℤ_[ℓ] (L j)] (V : ∀ j, abelian₂ →ₗ[ℤ_[ℓ]] L j)
      (β : ∀ j, L j ≃ₗ[ℤ_[ℓ]] L j),
    (∀ t : ∀ j, L j, ∃ la : abelian₂, V 1 la = ((ℓ : ℤ_[ℓ]) ^ (s - 1)) • t 1 ∧
      ∀ j, 2 ≤ j → j ≤ s → V j la = ((ℓ : ℤ_[ℓ]) ^ (s - j + 1)) • t j) →
    ∀ ω : ∀ j, L j, ∃ la : abelian₂, ∀ j, 1 ≤ j → j ≤ s →
      (((u ^ e : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) • (((ℓ : ℤ_[ℓ]) ^ (e * (s - j))) • β j (V j la))
        = ((ℓ : ℤ_[ℓ]) ^ ((e + 1) * (s - 1) + s + padicValNat ℓ e)) • ω j

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
