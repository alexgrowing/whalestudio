import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFamilyPairingIntegralCommute
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_family_pairing_integral_commute : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure W) (T : SchwartzMap V ℂ →L[ℂ] ℂ) (Φ : W → SchwartzMap V ℂ), Continuous Φ →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ w x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Φ w) x‖ ≤ C * (1 + ‖w‖) ^ n) →
    ∀ φ : W → ℂ, AEStronglyMeasurable φ μ → (∀ n : ℕ, Integrable (fun w => (1 + ‖w‖) ^ n * ‖φ w‖) μ) →
    ∀ h : SchwartzMap V ℂ, (∀ (n : ℕ) (x : V), iteratedFDeriv ℝ n h x = ∫ w, φ w • iteratedFDeriv ℝ n (Φ w) x ∂μ) →
    T h = ∫ w, φ w * T (Φ w) ∂μ := by
  first | exact @GlobalTheory.clm_integral_exchange | exact GlobalTheory.clm_integral_exchange | (intros; apply GlobalTheory.clm_integral_exchange <;> assumption)
