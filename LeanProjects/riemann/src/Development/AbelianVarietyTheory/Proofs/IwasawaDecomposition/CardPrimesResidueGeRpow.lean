import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.PrimesInProgressionCountLowerBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimesAPIntervalOfTzRat
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem card_primes_residue_ge_rpow :
    GlobalTheory.Mem.An.TZRat → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ m₀ a₀ : ℕ, 3 ≤ m₀ → Nat.Coprime a₀ m₀ → ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → X ^ ((9 : ℝ) / 10) ≤ ((Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X).card : ℝ) := by
  intro h eps h0 h1
  obtain ⟨C₀, Cr, cr, c, hC₀, hCr, hcr, hc, hP⟩ := GlobalTheory.Mem.An.primesAPInterval_of_tzRat h
  exact Formalism.HermitianLattices.GL2PrimeSums.primesInProgressionCountLowerBound C₀ Cr cr c hC₀ hCr hcr hc hP eps h0 (by linarith)

end GlobalTheory.Mem.An
