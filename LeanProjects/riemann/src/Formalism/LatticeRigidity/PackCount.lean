import Mathlib

namespace Formalism.SA.P7

def PackCount : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (V : ι → Type) [∀ v, NormedAddCommGroup (V v)]
    [∀ v, NormedSpace ℝ (V v)] [∀ v, FiniteDimensional ℝ (V v)] (N : ℕ),
    (∀ v, Module.finrank ℝ (V v) = N) →
    ∀ (S : Finset (∀ v, V v)) (lam : ℝ) (X : ι → ℝ), 0 < lam → (∀ v, 0 < X v) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        lam ≤ (∏ v, ‖x v - y v‖) ^ ((1 : ℝ) / Fintype.card ι)) →
      (∀ x ∈ S, ∀ v, ‖x v‖ ≤ X v) →
      (S.card : ℝ) ≤
        (1 + 2 * (∏ v, X v) ^ ((1 : ℝ) / Fintype.card ι) / lam) ^ (N * Fintype.card ι)

end Formalism.SA.P7
