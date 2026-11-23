import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowSubstitutionCoeffExponentLeDegree
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericRowSubstitution_coeff_exponent_le_degree : ∀ (O : Type) [CommRing O] (N : ℕ) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → ∀ m, (GlobalTheory.HighWt.genSub O N f).coeff m ≠ 0 → ∀ v, m v ≤ D := by
  first | exact @GlobalTheory.GenSubDeg.genSub_coeff_le | exact GlobalTheory.GenSubDeg.genSub_coeff_le | (intros; apply GlobalTheory.GenSubDeg.genSub_coeff_le <;> assumption)
