import Mathlib
import Formalism.GrowthSums.StatementA

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

def CappedGainSubLE : Prop :=
  ∀ (n : ℕ) (p : ℝ) (TT TTodd : Finset (ZMod n)) (al cap : ZMod n → ℝ) (de v i₀ : ℝ)
    (i : ZMod n → ℕ → ℝ) (E : Finset ℕ),
    1 < p → TTodd ⊆ TT → (∀ s, 0 ≤ al s) → (∀ s, 0 ≤ cap s) →
    (∀ s e, 0 ≤ i s e) → (∀ s e, e ∉ E → i s e = 0) →
    gamP p * ∑ s ∈ TT, al s - i₀ - ∑ s ∈ TT, ∑ e ∈ E, i s e - de ≤ v →
    i₀ + ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e ≤ ∑ s ∈ TT \ TTodd, al s →
    (∀ s ∈ TTodd, ∀ e, i s e ≤ min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))) →
    gainG p TT TTodd al cap de - ∑ s ∈ TT \ TTodd, al s ≤ v

def ShiftedRows : Prop :=
  ∀ ρ c c' A u θ : ℝ, 0 ≤ ρ → ρ ≤ c → ρ ≤ A → 0 ≤ u → ρ + c' = c + A - u →
    ρ * c' = c * A - (c - ρ) * (A - ρ) - ρ * u ∧ ρ * c' ≤ c * A ∧
    (0 < c → 0 < A → 0 ≤ θ → θ < 1 / 4 → (1 - θ) * (c * A) ≤ ρ * c' →
      min c A / 2 ≤ ρ ∧ u ≤ 2 * θ * max c A)

def BackwardProduct : Prop :=
  ∀ (s : ℕ) (ρ c A : ℕ → ℝ), (∀ i < s, 0 ≤ ρ i ∧ 0 ≤ A i ∧ ρ i * c (i + 1) ≤ c i * A i) →
    0 ≤ c s → ∀ i ≤ s, (∏ l ∈ Ico i s, ρ l) * c s ≤ c i * ∏ l ∈ Ico i s, A l

def RootInterval : Prop :=
  ∀ (ρ : ℝ) (d : ℕ), 0 ≤ ρ → ρ ≤ 1 / 2 → 1 ≤ d →
    (1 + ρ) ^ ((1 : ℝ) / d) - (1 - ρ) ^ ((1 : ℝ) / d) ≤ 3 * ρ

end Formalism.GrowthSums
