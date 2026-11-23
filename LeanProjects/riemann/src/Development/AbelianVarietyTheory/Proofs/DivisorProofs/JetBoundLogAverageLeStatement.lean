import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetBoundLogAverageLe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequalityStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.MatrixArithmetic.WeakMatSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_bound_log_average_le : ∀ (g : ℕ) (K : Type) [Field K] [NumberField K] (ρ : (K →+* ℂ) → ℝ) (H : ℝ) (n' i : ℕ), 0 ≤ H → (∀ σ, 0 < ρ σ) → (∑ σ, (ρ σ ^ 2)⁻¹) / (Module.finrank ℚ K : ℝ) ≤ 14 * (1 + H + Real.log (Nat.factorial g)) → 1 ≤ n' → i ≤ n' → (∑ σ, Real.log (jetBd g (4 * n') i (ρ σ))) / (Module.finrank ℚ K : ℝ) ≤ (i : ℝ) / 2 * Real.log (Real.exp 1 * (4 * n') * n') + (1 / 2 + Real.log (Nat.factorial g) / 2 + (g / 2) * Real.log (4 * n') + g * ((Real.log (4 / Real.pi) + Real.log (15 + 14 * Real.log (Nat.factorial g))) / 2) + (g / 2) * Real.log (2 + H)) := by
  first | exact @GlobalTheory.jetBd_log_mean_le | exact GlobalTheory.jetBd_log_mean_le | (intros; apply GlobalTheory.jetBd_log_mean_le <;> assumption)
