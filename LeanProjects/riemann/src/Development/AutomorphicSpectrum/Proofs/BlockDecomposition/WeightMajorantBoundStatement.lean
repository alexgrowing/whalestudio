import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightMajorantBound
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Qf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula
open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_majorant_bound : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, ∀ (N : ℕ) (h : M22), 0 < (Matrix.of h).det → (1 + uu h) ^ 2 * ‖w0 k h‖ * |(Matrix.of h).det|⁻¹ / ((1 + ‖h‖) ^ N * (1 + ‖Ad3.LR.B.eta h‖) ^ N) ≤ C * Ad3.LR.B.maj k N (1 / 2) 1 h := by
  first | exact @GlobalTheory.CompanionTheory.DInt2.WMaj.main | exact GlobalTheory.CompanionTheory.DInt2.WMaj.main | (intros; apply GlobalTheory.CompanionTheory.DInt2.WMaj.main <;> assumption)
