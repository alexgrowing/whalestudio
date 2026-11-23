import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereDensityBound
import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
open ReciprocityTheory.AnForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_density_bound : ∀ {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (c : Fin e → ℝ), ContDiffAt ℝ 2 f z → (∀ w, 0 ≤ levi f z w) → (∀ w, levi f z w ≤ ∑ k, c k * ‖w k‖ ^ 2) → maDens (fun _ => f) z ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * ∏ k, c k := by
  first | exact @GlobalTheory.maDens_le_prod_of_levi_le_diag | exact GlobalTheory.maDens_le_prod_of_levi_le_diag | (intros; apply GlobalTheory.maDens_le_prod_of_levi_le_diag <;> assumption)
