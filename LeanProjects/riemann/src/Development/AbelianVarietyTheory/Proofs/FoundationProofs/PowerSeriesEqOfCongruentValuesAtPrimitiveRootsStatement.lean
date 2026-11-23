import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesEqOfCongruentValuesAtPrimitiveRoots
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_eq_of_congruent_values_at_primitiveRoots : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (A B : PowerSeries (Qbar l)) (u : Qbar l) (w : ℕ → Qbar l) (c₀ m₀ : ℕ), (∀ n, A.coeff n ∈ c.O) → (∀ n, B.coeff n ∈ c.O) → B ≠ 0 → ‖u‖ = 1 → (∀ m, ‖w m‖ = 1 ∧ Cg m (w (m + 1)) (w m)) → (∀ m, m₀ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg (m / 2 - c₀) (tval A (l ^ (3 * m)) z) (w m * u ^ m * tval B (l ^ (3 * m)) z)) → u = 1 ∧ ∀ k : ℕ, ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ n, Cg k (A.coeff n) (w m * B.coeff n) := by
  first | exact @GlobalTheory.KZ.autoPin_congr | exact GlobalTheory.KZ.autoPin_congr | (intros; apply GlobalTheory.KZ.autoPin_congr <;> assumption)
