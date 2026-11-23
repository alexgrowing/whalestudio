import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianDetSquareIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_det_square_integral : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (G : Matrix β (Fin d) ℂ), ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (‖(Matrix.of C * G).det‖ ^ 2) = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (G.conjTranspose * G).det.re) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq | exact GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq <;> assumption)
