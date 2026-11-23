import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivCexpPhaseLe
import Mathlib

open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_cexp_phase_le' : ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h → (∀ y t, (B y t + h t).re = 0) → ∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t)) t‖ ≤ C * (1 + ‖y‖) ^ n := by
  first | exact @GlobalTheory.norm_iteratedFDeriv_cexp_phase_le | exact GlobalTheory.norm_iteratedFDeriv_cexp_phase_le | (intros; apply GlobalTheory.norm_iteratedFDeriv_cexp_phase_le <;> assumption)
