import Formalism.LogVandermondeBounds.LogRatioLowerBound

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def VandPlace : Prop :=
  ∀ (ε x : ℝ), 0 < ε → 1 ≤ x → ∀ (k m : ℕ) (Δ : ℝ) (u v b w : ℕ → ℝ), 2 ≤ k → 1 ≤ m → 1 ≤ Δ →
    PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m u v b w →
    0 < vandN u k ∧ 0 < vandN (rowPar k v b) (k - 1 + m) ∧
    ((k : ℝ) - 1) * ∑ j ∈ range m, Real.log (b j)
      - 2 * k * Real.log (8 * (x * Real.exp (x ^ ε))) - 2 * k * (1 + Real.log k)
      ≤ Real.log (vandN (rowPar k v b) (k - 1 + m)) - Real.log (vandN u k)

end Formalism.LogVandermondeBounds.StandardLattice
