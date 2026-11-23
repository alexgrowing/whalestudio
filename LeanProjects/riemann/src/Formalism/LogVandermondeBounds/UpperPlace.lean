import Formalism.LogVandermondeBounds.LogRatioUpperBound

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def UpperPlace : Prop :=
  ∀ (ε x : ℝ), 0 < ε → 1 ≤ x → ∀ (k m : ℕ) (Δ C₃ : ℝ) (u v b w : ℕ → ℝ),
    2 ≤ m → Even m → 2 ≤ k → (m : ℝ) ≤ k → 1 ≤ Δ → 1 ≤ C₃ →
    PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m u v b w →
    (∀ i j, i < j → j < k → 1 ≤ u i - u j) →
    0 < dimVN u k ∧ 0 < dTau k m (rowPar k v b) ∧
    Real.log (4 * dTau k m (rowPar k v b) *
        (C₃ * ((k - 1 + m / 2 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) * ((k - 1 + m : ℕ) : ℝ) * (v 0 + b (m - 1))) ^
          ((k - 1 + m / 2) * (m / 2))) - Real.log (dimVN u k)
      ≤ (k : ℝ) * m * (Real.log C₃ + 5 * Real.log (2 * k) + 5 * x ^ ε + 10)

end Formalism.LogVandermondeBounds.StandardLattice
