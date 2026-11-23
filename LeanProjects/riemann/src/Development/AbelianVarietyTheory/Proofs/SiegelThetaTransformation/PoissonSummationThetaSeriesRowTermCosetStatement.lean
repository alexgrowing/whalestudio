import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PoissonSummationThetaSeriesRowTermCoset
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EchEqOneIff
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_thetaSeriesRowTerm_coset : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : ℕ), 0 < R → ∀ τ ∈ Siegel ι, -τ⁻¹ ∈ Siegel ι → IsUnit τ.det → ∃ c : ℂ, c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det) = 1 ∧ ∀ (a : ι → ℚ) (ζ : ι → ℂ), (Summable fun m : ι → ℤ => ‖gs τ ζ (a + (R : ℚ) • zv m)‖) ∧ (Summable fun m : ι → ℤ => ‖gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • zv m)‖) ∧ cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) * ∑' m : ι → ℤ, gs τ ζ (a + (R : ℚ) • zv m) = c * ∑' m : ι → ℤ, ech (a ⬝ᵥ ((R : ℚ)⁻¹ • zv m)) * gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • zv m) := by
  first | exact @GlobalTheory.SW.FourierJ.Row.poisson_class | exact GlobalTheory.SW.FourierJ.Row.poisson_class | (intros; apply GlobalTheory.SW.FourierJ.Row.poisson_class <;> assumption)
