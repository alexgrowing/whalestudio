import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicativeWeightPrimeSum
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_weight_prime_sum : GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ m₀ a₀ : ℕ, 8 ∣ m₀ → 0 < m₀ → Nat.Coprime a₀ m₀ → a₀ % 4 = 3 → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (eps / 5) ∨ x ^ (400 : ℝ) < p) → ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → ∀ κ : ℕ → ℂ, κ 1 = 1 → (∀ m n, κ (m * n) = κ m * κ n) → (∀ n, ‖κ n‖ ≤ 1) → (∑ p ∈ Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X, ‖Formalism.HermitianLattices.GL2PrimeSums.sqSum x κ p‖ ^ 2) / (Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X).card ≤ C * x * Real.log x := by
  first | exact @GlobalTheory.Mem.An.meanSq_primes_residue_le | exact GlobalTheory.Mem.An.meanSq_primes_residue_le | (intros; apply GlobalTheory.Mem.An.meanSq_primes_residue_le <;> assumption)
