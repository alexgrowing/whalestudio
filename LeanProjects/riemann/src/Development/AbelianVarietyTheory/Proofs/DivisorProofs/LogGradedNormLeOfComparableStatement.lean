import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGradedNormLeOfComparable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_graded_norm_le_of_comparable : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) (m : ℝ), 1 ≤ m → A.PosDef → B.PosDef → (((m : ℂ) • B) - A).PosSemidef → (((m : ℂ) • A) - B).PosSemidef → ∀ i : Fin n, |Real.log (GlobalTheory.GradedNorm.grSq A i) - Real.log (GlobalTheory.GradedNorm.grSq B i)| ≤ 2 * n * Real.log m := by
  first | exact @GlobalTheory.GradedNorm.Comparable.graded_log_bound | exact GlobalTheory.GradedNorm.Comparable.graded_log_bound | (intros; apply GlobalTheory.GradedNorm.Comparable.graded_log_bound <;> assumption)
