import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLineSelfIntersectionZeroOfEqual
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
open GlobalTheory.CovTop GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_line_selfIntersection_zero_of_equal : Hypotheses2 → ∀ (ι : Type) [Fintype ι] (N : ℕ) (lam : ι → Fin N → ℤ) (j : ℕ) (τ : ι), 1 ≤ j → j < N → (∀ a b : Fin N, (b : ℕ) = a + 1 → (b : ℕ) = j → lam τ a = lam τ b) → (wtLine lam).IsSelfInter 0 := by
  first | exact @GlobalTheory.FlagZ.WeightDrop.isSelfInter_wtLine_zero | exact GlobalTheory.FlagZ.WeightDrop.isSelfInter_wtLine_zero | (intros; apply GlobalTheory.FlagZ.WeightDrop.isSelfInter_wtLine_zero <;> assumption)
