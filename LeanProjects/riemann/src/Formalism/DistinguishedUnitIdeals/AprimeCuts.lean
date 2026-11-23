import Mathlib
import Formalism.DistinguishedUnitIdeals.Statement
import Formalism.TruncatedSeriesCounting.AprimeArith

noncomputable section

namespace Formalism.ExponentWindows

def AprimeCuts : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, 11 ≤ ℓ →
    ∀ (n j : ℕ) [NeZero n] (size : ZMod n → ℕ) (b w S η : ℕ) (rr : ℝ),
      1 ≤ j → j + 1 ≤ n →
      (∀ i, (b ≤ size i ∧ size i ≤ b + η) ∨ size i ≤ w) →
      C * ((j : ℝ) + 1) * ((w + S + η : ℕ) + 1 : ℝ) ≤ b →
      (∀ a : ZMod n, (b ≤ size a ∧ size a ≤ b + η) → ∀ k : ℕ, 1 ≤ k → k ≤ j →
        (b ≤ size (a - k) ∧ size (a - k) ≤ b + η) →
        ∀ k' : ℕ, 1 ≤ k' → k' ≤ j → ¬ (b ≤ size (a - k - k') ∧ size (a - k - k') ≤ b + η)) →
      rr ≤ 20 * (((w + S + η : ℕ) : ℝ) / ℓ + ((b + η + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) +
        Real.logb ℓ (b + η + S : ℕ) + 1) →
      ∃ (cuts : Finset (ZMod n)) (ell : ZMod n → ℕ), cuts.Nonempty ∧
        ∀ c ∈ cuts,
          (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ (b ≤ size (c + k) ∧ size (c + k) ≤ b + η)) ∧
          j ≤ ell c ∧ ell c ≤ 3 * j + 1 ∧ c - (ell c : ZMod n) ∈ cuts ∧
          (∀ k : ℕ, 1 ≤ k → k < ell c → c - k ∉ cuts) ∧
          ((Finset.range (ell c)).filter
            (fun k : ℕ => b ≤ size (c - (k : ZMod n)) ∧ size (c - (k : ZMod n)) ≤ b + η)).card ≤ 2 ∧
          (∀ k : ℕ, k < ell c → (b ≤ size (c - k) ∧ size (c - k) ≤ b + η) →
            max (w + S + η) 1 < size (c - k)) ∧
          (∀ k k' : ℕ, k < ell c → k' < k →
            (b ≤ size (c - k) ∧ size (c - k) ≤ b + η) →
            (b ≤ size (c - k') ∧ size (c - k') ≤ b + η) →
            (size (c - k') : ℝ) < ℓ * size (c - k) ∧ (size (c - k') : ℝ) ≤ ℓ * size (c - k) / 2 ∧
            Formalism.TruncatedSeriesCounting.WachCoordinates.a0E ℓ (max (w + S + η) 1) (b + η + S) j (3 * j + 1) rr <
              (size (c - k) : ℝ) / 2)

end Formalism.ExponentWindows
