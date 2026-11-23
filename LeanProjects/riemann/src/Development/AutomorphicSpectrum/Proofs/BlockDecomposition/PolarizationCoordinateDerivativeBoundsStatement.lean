import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarizationCoordinateDerivativeBounds
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Qf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula
open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_coordinate_derivative_bounds : ∀ (a b c d : Fin 2) (h : M22), 0 < (Matrix.of h).det → DifferentiableAt ℝ (rho c d) h ∧ DifferentiableAt ℝ tt h ∧ ‖fderiv ℝ (rho c d) h (rpol a b h)‖ ≤ 2 ∧ ‖fderiv ℝ tt h (rpol a b h)‖ ≤ 3 * uu h := by
  first | exact @GlobalTheory.CompanionTheory.DInt2.Drho.main | exact GlobalTheory.CompanionTheory.DInt2.Drho.main | (intros; apply GlobalTheory.CompanionTheory.DInt2.Drho.main <;> assumption)
