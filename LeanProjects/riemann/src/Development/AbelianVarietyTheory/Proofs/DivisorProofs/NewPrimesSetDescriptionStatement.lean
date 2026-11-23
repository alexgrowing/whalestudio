import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NewPrimesSetDescription
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.new_primes_set_description : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ B₀ B : ℝ, 0 ≤ B₀ → (B₀ ≤ B → setB Y B₀ ⊆ setB Y B) ∧ (∀ p ∈ setB Y B, p.Prime) ∧ (∀ p : ℕ, p ∈ newPrimes Y B₀ B ↔ p.Prime ∧ B₀ < p ∧ p ≤ ⌊B⌋₊ ∧ ¬ p ∣ 2 * dE D ∧ p ∉ Y.lev) ∧ ∀ n : ℕ, newPrimes Y B₀ n = (Finset.range (n + 1)).filter (fun p : ℕ => p.Prime ∧ B₀ < (p : ℝ) ∧ ¬ p ∣ 2 * dE D ∧ p ∉ Y.lev) := by
  first | exact @GlobalTheory.Mean4.setB_newP_facts | exact GlobalTheory.Mean4.setB_newP_facts | (intros; apply GlobalTheory.Mean4.setB_newP_facts <;> assumption)
