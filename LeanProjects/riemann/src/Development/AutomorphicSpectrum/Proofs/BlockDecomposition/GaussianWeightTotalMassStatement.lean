import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianWeightTotalMass
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_weight_total_mass : ∀ (d : ℕ) (α : Type) [Fintype α], ∫⁻ C : Fin d → α → ℂ, gW d α C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW | exact GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW <;> assumption)
