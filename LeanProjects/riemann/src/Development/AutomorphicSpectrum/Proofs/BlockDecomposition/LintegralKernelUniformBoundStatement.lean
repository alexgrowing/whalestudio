import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelUniformBound
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_kernel_uniform_bound : ∀ s : ℝ, 0 < s → ∃ K : ℝ, 0 ≤ K ∧ ∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern s T₀ z) ≤ ENNReal.ofReal K := by
  first | exact @GlobalTheory.CompanionTheory.MajC.KernInt.lintegral_kern_le | exact GlobalTheory.CompanionTheory.MajC.KernInt.lintegral_kern_le | (intros; apply GlobalTheory.CompanionTheory.MajC.KernInt.lintegral_kern_le <;> assumption)
