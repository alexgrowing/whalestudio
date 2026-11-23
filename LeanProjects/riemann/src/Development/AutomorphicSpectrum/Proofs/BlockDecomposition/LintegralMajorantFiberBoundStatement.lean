import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralMajorantFiberBound
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_majorant_fiber_bound : ∀ (ε K : ℝ), 0 < ε → 0 ≤ K → (∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern (2 * ε) T₀ z) ≤ ENNReal.ofReal K) → ∀ N : ℕ, 2 * ε ≤ N → ∀ (h : M22) (a b : ℂ), a ≠ 0 → 0 < dt h → 0 < ‖eta h‖ → ∫⁻ t : ℂ, ENNReal.ofReal (jm N h t a b) ≤ ENNReal.ofReal (K * ‖a‖ ^ (-ε) * dt h ^ (-2 + ε) * ‖eta h‖ ^ (-2 + 2 * ε) * ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.MajC.TB.lintegral_jm_le | exact GlobalTheory.CompanionTheory.MajC.TB.lintegral_jm_le | (intros; apply GlobalTheory.CompanionTheory.MajC.TB.lintegral_jm_le <;> assumption)
