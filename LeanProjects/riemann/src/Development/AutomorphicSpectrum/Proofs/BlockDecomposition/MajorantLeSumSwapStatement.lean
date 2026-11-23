import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantLeSumSwap
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_le_sum_swap : ∀ (ε β : ℝ) (m N : ℕ), 0 < ε → 0 < β → 2 * ε ≤ m → 2 * m ≤ N → ∀ h : M22, hm ε N β h ≤ gm ε β m h + gm ε β m (swp h) := by
  first | exact @GlobalTheory.CompanionTheory.MajC.hm_le_gm_add | exact GlobalTheory.CompanionTheory.MajC.hm_le_gm_add | (intros; apply GlobalTheory.CompanionTheory.MajC.hm_le_gm_add <;> assumption)
