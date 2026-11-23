import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section

open Polynomial GlobalTheory.GLq

namespace GlobalTheory.Published

def IsRegularChar (g d : ℕ) {K : Type} [Field K] (θ : Kˣ →* ℂˣ) : Prop :=
  ∀ i j, i < d → j < d → θ ^ g ^ i = θ ^ g ^ j → i = j

def GreenRegularCharacters : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Module.finrank (ZMod g) K = d →
    ∃ τ : (Kˣ →* ℂˣ) → Gn g d → ℂ,
      (∀ θ, IsRegularChar g d θ → IsCusp (τ θ) ∧ τ θ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ∧
        ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g d).charpoly = 0 →
          τ θ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) ∧
      (∀ θ θ', IsRegularChar g d θ → IsRegularChar g d θ' → (τ θ = τ θ' ↔ ∃ i < d, θ' = θ ^ g ^ i)) ∧
      ∀ χ : Gn g d → ℂ, IsCusp χ → ∃ θ, IsRegularChar g d θ ∧ χ = τ θ

end GlobalTheory.Published

end
