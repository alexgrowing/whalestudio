import Formalism.RankGapBounds.RankAndGapBounds
import Formalism.RankGapBounds.RandomSubsetCounterexample
import Formalism.RankGapBounds.ConjInOrbit

namespace Formalism.RankGapBounds.V4

open Formalism.RankGapBounds.LocalQuadraticParts Formalism.RankGapBounds.ExistsSmulMemTer

def RankGapPrintedLemma : Prop :=
  ∀ (α ι : Type) [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)],
    0 < δ → δ ≤ 1 → 16 ≤ δ * Fintype.card α → 0 ≤ β → (∀ p, 0 ≤ ω p) →
    (∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T), wt δ T ≤ β * δ) →
    ∃ T : Finset α, δ * Fintype.card α / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card α ∧
      ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ p, ω p

def ConjInOrbitAll : Prop :=
  ∀ (e : ℕ) (φ : GG e), cc e ∈ AddSubgroup.zmultiples φ ↔ φ = cc e

def RankGapDecayHypothesis : Prop :=
  ∀ n m γ : ℝ, 3 ≤ n → 1 ≤ m → m ≤ n → n ^ 7 ≤ γ →
    120 * n * (m / 2) ^ ((3 : ℝ) / 2) ≤ γ

structure GridNumericalHypotheses (k m t r : ℕ) (h₀ : ℝ) : Prop where
  k_even : Even k
  m_even : Even m
  m_pos : 1 ≤ m
  r_def : r + 1 = k + m
  k_ge : m + 3 ≤ k
  t_odd : Odd t
  t_gt_m : 3 * m < t
  t_gt_r : r + 4 < t
  h₀_big : (t : ℝ) + 2 * ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < h₀

def RankGapBoundPair : Prop :=
  ∀ (k m t r : ℕ) (h₀ γ : ℝ), GridNumericalHypotheses k m t r h₀ →
    2 * ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 + 2 * ((r + 6 : ℕ) : ℝ) + 2 < γ →
    (∀ i j : ℕ, i ≤ m → j ≤ m → r + j * t + i * (r + 6) < k + m * (t + (r + 6) + 1)) ∧
    (∀ i : ℕ, i ≤ m → (r + 1) + i * (r + 5) < k + m * (t + (r + 6) + 1)) ∧
    (∀ M : ℕ, M < k + m * (t + (r + 6) + 1) →
      (M : ℝ) ^ 3 < (h₀ - t) / 2 ∧ (M : ℝ) ^ 3 < γ / 2 - ((r + 6 : ℕ) : ℝ)) ∧
    ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < (h₀ - t) / 2 ∧
    ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < γ / 2 - ((r + 6 : ℕ) : ℝ) ∧
    (((r + 6 : ℕ) : ℝ) + 1) / 2 ≤ γ / 2 - 1 ∧ ((r + 6 : ℕ) : ℝ) / 2 ≤ γ / 2 - 1 ∧
    γ / 2 - ((r + 6 : ℕ) : ℝ) ≤ γ / 2 - 1 - (((r + 6 : ℕ) : ℝ) - 1) / 2

end Formalism.RankGapBounds.V4
