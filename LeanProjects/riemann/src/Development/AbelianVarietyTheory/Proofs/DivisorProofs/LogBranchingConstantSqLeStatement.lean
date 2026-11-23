import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBranchingConstantSqLe
import Mathlib
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq

open Formalism.BasicNotions

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_branching_constant_sq_le : ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (B : ℝ), 1 ≤ B → (N : ℝ) ≤ B → (∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) → Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd h lam sg ^ 2) ≤ 5 * N * B * Real.log (6 * B) := by
  first | exact @GlobalTheory.BranchBound.log_brBd_sq_le | exact GlobalTheory.BranchBound.log_brBd_sq_le | (intros; apply GlobalTheory.BranchBound.log_brBd_sq_le <;> assumption)
