import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarJacLeExp
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarJac_le_exp_hsNorm : ∀ (p q : ℕ) (h : ℕ → ℝ), (∏ i ∈ Finset.range (min p q), shc (2 * h i) * shc (h i) ^ (2 * (max p q - min p q))) * (∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1) ≤ Real.exp (((p + q : ℕ) : ℝ) * Real.sqrt (2 * (min p q : ℕ)) * hsNorm (aOf p q h)) := by
  first | exact @GlobalTheory.PolarJacBound.polarJac_le_exp | exact GlobalTheory.PolarJacBound.polarJac_le_exp | (intros; apply GlobalTheory.PolarJacBound.polarJac_le_exp <;> assumption)
