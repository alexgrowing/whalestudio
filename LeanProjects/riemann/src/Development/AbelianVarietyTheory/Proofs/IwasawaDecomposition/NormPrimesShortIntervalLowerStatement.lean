import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPrimesShortIntervalLower
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.QuadraticHeckeZeroEstimates
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_primes_short_interval_lower : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 1 ≤ M → ∀ X h : ℝ, (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ C₀ ≤ X → h ≤ 1 → Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr (4 * (d : ℝ) * (M : ℝ) ^ 2) X ≤ h / 100 → (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) → c * h * (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ (-6 : ℝ) * X / Real.log X ≤ ((normPrimes d M X (X * (1 + h))).card : ℝ) := by
  first | exact @GlobalTheory.Mem.NormPrimes.normPrimes_short_interval | exact GlobalTheory.Mem.NormPrimes.normPrimes_short_interval | (intros; apply GlobalTheory.Mem.NormPrimes.normPrimes_short_interval <;> assumption)
