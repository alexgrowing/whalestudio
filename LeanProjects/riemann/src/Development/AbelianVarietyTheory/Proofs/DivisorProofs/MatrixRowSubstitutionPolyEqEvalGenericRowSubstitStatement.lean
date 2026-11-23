import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyEqEvalGenericRowSubstit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixRowSubstitutionPoly_eq_eval_genericRowSubstitution : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O), rowSubst O N R Y f = ∑ m ∈ (GlobalTheory.HighWt.genSub O N f).support, (m.prod fun v k => Y v.1 v.2 ^ k) • MvPolynomial.map (algebraMap O R) ((GlobalTheory.HighWt.genSub O N f).coeff m) := by
  first | exact @GlobalTheory.GenCoef.RowSubstSum.main | exact GlobalTheory.GenCoef.RowSubstSum.main | (intros; apply GlobalTheory.GenCoef.RowSubstSum.main <;> assumption)
