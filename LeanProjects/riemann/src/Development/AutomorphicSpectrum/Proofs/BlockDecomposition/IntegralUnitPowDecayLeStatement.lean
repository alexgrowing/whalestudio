import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralUnitPowDecayLe
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantScaled
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelUniformBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantLeSumSwap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateLocalL1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Ga
open MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unit_pow_decay_le : ∀ σ : ℝ, σ < 1 → ∀ N : ℕ, 4 - 4 * σ ≤ N → ∃ K : ℝ, ∀ q : ℝ, 0 < q →
    Integrable (fun t : ℂˣ => ‖(t : ℂ)‖ ^ (2 * σ - 2) / (1 + ‖(t : ℂ)⁻¹‖ * q) ^ N) Ad3.K.mulC ∧
    ∫ t : ℂˣ, ‖(t : ℂ)‖ ^ (2 * σ - 2) / (1 + ‖(t : ℂ)⁻¹‖ * q) ^ N ∂Ad3.K.mulC ≤ K * q ^ (2 * σ - 2) := by
  first | exact @GlobalTheory.CompanionTheory.MajC.TInt.tint | exact GlobalTheory.CompanionTheory.MajC.TInt.tint | (intros; apply GlobalTheory.CompanionTheory.MajC.TInt.tint <;> assumption)
