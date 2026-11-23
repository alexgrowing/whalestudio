import Formalism.IncomingBounds.LevelTail

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

def InvWeight : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ n n' : ℤ, ((l : ℤ) ^ 2 - 1) ∣ (n - l * n') →
    ∃ k : ℤ, ((n : ℝ) + n') * rho l = k + (n' : ℝ) / ((l : ℝ) - 1)

def BinomGcd : Prop :=
  ∀ l : ℕ, l.Prime → ∀ n : ℕ, 2 ≤ n →
    ((∃ k, 0 < k ∧ k < n ∧ ¬ l ∣ n.choose k) ↔ ¬ ∃ e : ℕ, n = l ^ e) ∧
      ∀ e : ℕ, 1 ≤ e → n = l ^ e → ∃ k, 0 < k ∧ k < n ∧ ¬ l ^ 2 ∣ n.choose k

def FactValBounds : Prop :=
  ∀ l : ℕ, l.Prime → ∀ N : ℕ, 1 ≤ N →
    (N : ℝ) / ((l : ℝ) - 1) - (Real.logb l N + 1) ≤ (padicValNat l N.factorial : ℝ) ∧
      (padicValNat l N.factorial : ℝ) ≤ ((N : ℝ) - 1) / ((l : ℝ) - 1)

def UProduct : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ x : ℕ,
    uFac l x = (-((l - 1).factorial : ℚ)) ^ x *
      ∏ y ∈ Finset.range x, ∏ i ∈ Finset.Ico 1 l, (1 + (l : ℚ) * y / i)

def LogCoeffVal : Prop :=
  ∀ l : ℕ, l.Prime → 5 ≤ l → ∀ s : ℕ, 1 ≤ s →
    1 / ((l : ℝ) - 1) + ((s : ℝ) + 1) / 4 ≤ (s : ℝ) - padicValNat l s

def LemmaMExponent : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ s0 : ℕ,
    1 + (l : ℝ) * (∑ t ∈ Finset.range s0, ((l : ℝ) ^ 2) ^ t) =
        1 + ((l : ℝ) ^ (2 * s0 + 1) - l) * rho l ∧
      ∀ s : ℕ, (∑ t ∈ Finset.range (s + 1), ((l : ℝ) ^ 2) ^ t) =
        (l : ℝ) ^ 2 * (∑ t ∈ Finset.range s, ((l : ℝ) ^ 2) ^ t) + 1

def LemmaMNumerics : Prop :=
  ∀ l : ℕ, 5 ≤ l → ∀ i : ℕ, Odd i →
    (l : ℝ) ^ 2 * rho l = 1 + rho l ∧
    (∀ i' : ℕ, 3 ≤ i' → (l : ℝ) - 2 ≤ (l : ℝ) ^ i' * rho l - ((i' : ℝ) - 1)) ∧
    (∀ i' : ℕ, 2 ≤ i' → 0 < (l : ℝ) ^ i' * rho l - ((i' : ℝ) - 1) ∧ 0 < (l : ℝ) ^ i' - i') ∧
    1 + rho l ≤ (l : ℝ) * (1 + rho l) - 1 ∧
    ((l : ℝ) ^ 2) ^ ((i + 1) / 2) * (3 * ((l : ℝ) ^ i)⁻¹ / 8) = 3 * (l : ℝ) / 8 ∧
    1 < 3 * (l : ℝ) / 8 ∧
    1 / ((l : ℝ) - 1) - (rho l + 1 / 2 - ((l : ℝ) ^ i)⁻¹ / 8) < 0 ∧
    1 / 2 - 1 / (8 * (l : ℝ)) ≤ rho l + 1 / 2 - ((l : ℝ) ^ i)⁻¹ / 8 ∧
    (∀ i' : ℕ, 1 ≤ i' → (i' : ℝ) < (l : ℝ) ^ i' / ((l : ℝ) - 1)) ∧
    ∀ J v : ℕ, 2 ≤ J → l ^ v ≤ J →
      let rm : ℝ := rho l + 1 / 2 - ((l : ℝ) ^ i)⁻¹ / 8
      (v = 0 → rm ≤ ((J : ℝ) - 1) * (rm - 1 / ((l : ℝ) - 1)) + rm - v) ∧
        (1 ≤ v → 3 / 8 ≤ ((J : ℝ) - 1) * (rm - 1 / ((l : ℝ) - 1)) + rm - v)

end Formalism.IncomingBounds
