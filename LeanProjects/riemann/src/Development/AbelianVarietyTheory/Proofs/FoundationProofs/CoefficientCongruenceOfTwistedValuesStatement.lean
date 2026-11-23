import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefficientCongruenceOfTwistedValues
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_congruence_of_twisted_values : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (k m₁ : ℕ), (∀ n, F.coeff n ∈ c.O) → (∀ m, m₁ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg k (tval F (l ^ (3 * m)) z) 0) → ∀ n, Cg k (F.coeff n) 0 := by
  first | exact @GlobalTheory.KZ.CoefVal.coeff_cg_of_values | exact GlobalTheory.KZ.CoefVal.coeff_cg_of_values | (intros; apply GlobalTheory.KZ.CoefVal.coeff_cg_of_values <;> assumption)
