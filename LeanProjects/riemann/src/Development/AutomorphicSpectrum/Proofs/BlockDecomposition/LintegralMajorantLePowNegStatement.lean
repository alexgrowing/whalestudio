import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralMajorantLePowNeg
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_majorant_le_pow_neg : ∀ (ε K : ℝ) (m : ℕ), 0 < ε → 0 ≤ K → (∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern ε T₀ z) ≤ ENNReal.ofReal K) → 3 ≤ m → 2 * ε ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β → ∫⁻ h : M22, ENNReal.ofReal (gm ε β m h) ≤ ENNReal.ofReal (C * β ^ (-ε)) := by
  first | exact @GlobalTheory.CompanionTheory.MajGm.gm_integral_le | exact GlobalTheory.CompanionTheory.MajGm.gm_integral_le | (intros; apply GlobalTheory.CompanionTheory.MajGm.gm_integral_le <;> assumption)
