import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantLeConstMulTorus
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
theorem _root_.GlobalTheory.T.majorant_le_const_mul_torus : ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ (C : ℝ) (N₀ : ℕ), ∀ N ≥ N₀, ∀ h : Ad3.K.LC.M22, ‖h 1 0‖ ≤ ‖h 0 0‖ → GlobalTheory.CompanionTheory.MajC.dt h ≠ 0 →
    GlobalTheory.CompanionTheory.PerUC.gx σ N h ≤ C * GlobalTheory.CompanionTheory.PerUC.ga σ 4 h := by
  first | exact @GlobalTheory.CompanionTheory.PerUC.GxLe.gx_le_ga | exact GlobalTheory.CompanionTheory.PerUC.GxLe.gx_le_ga | (intros; apply GlobalTheory.CompanionTheory.PerUC.GxLe.gx_le_ga <;> assumption)
