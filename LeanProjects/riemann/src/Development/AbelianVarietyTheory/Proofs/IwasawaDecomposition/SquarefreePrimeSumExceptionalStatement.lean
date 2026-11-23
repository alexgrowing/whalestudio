import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquarefreePrimeSumExceptional
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefree_prime_sum_exceptional : GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ m₀ a₀ : ℕ, 8 ∣ m₀ → 0 < m₀ → Nat.Coprime a₀ m₀ → ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → ∃ nStar : ℕ, ∀ s : ℕ, 1 < s → Squarefree s → Nat.Coprime s m₀ → (s : ℝ) ≤ x ^ (800 : ℝ) → s ≠ nStar → |(∑ p ∈ Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X, (jacobiSym (p : ℤ) s : ℝ)) / (Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X).card| ≤ C' * Real.exp (-c' * Real.log x ^ 2) := by
  first | exact @GlobalTheory.Mem.An.jacobi_mean_small | exact GlobalTheory.Mem.An.jacobi_mean_small | (intros; apply GlobalTheory.Mem.An.jacobi_mean_small <;> assumption)
