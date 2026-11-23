import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianDetLeviIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_det_levi_integral : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (f : β → ℂ) (F : Matrix β (Fin d) ℂ), ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * f j‖ ^ 2) * ‖(Matrix.of C * F).det‖ ^ 2) = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (fsLevi f F).det.re) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi | exact GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi <;> assumption)
