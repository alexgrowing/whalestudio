import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLineIsNefOfAntitone
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
open GlobalTheory.CovTop GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_line_isNef_of_antitone : Hypotheses2 → ∀ (ι : Type) [Fintype ι] (N : ℕ) (lam : ι → Fin N → ℤ), (∀ τ (a b : Fin N), a ≤ b → lam τ b ≤ lam τ a) → (wtLine lam).IsNef (dimFl ι N) := by
  first | exact @GlobalTheory.FlagZ.WtNef.wtLine_isNef | exact GlobalTheory.FlagZ.WtNef.wtLine_isNef | (intros; apply GlobalTheory.FlagZ.WtNef.wtLine_isNef <;> assumption)
