import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulUntiltFrobeniusDoubleSeriesEqZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_mul_untiltFrobeniusDoubleSeries_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (i : ℕ) (y : ℕ → Fin h → Fl l) (ρ : ℝ),
    1 ≤ h → ρ < 1 → (∀ k j, ‖sh (y k j)‖ ≤ ρ) →
    HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * ∑ j, μ j * lam h i (y k j)) 0 →
    ∑ j, μ j * abelian₂ h i (fun k => y k j) = 0 := by
  first | exact @GlobalTheory.PSer.sum_mul_Lam_eq_zero | exact GlobalTheory.PSer.sum_mul_Lam_eq_zero | (intros; apply GlobalTheory.PSer.sum_mul_Lam_eq_zero <;> assumption)
