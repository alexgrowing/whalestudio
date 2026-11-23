import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProdIicBlockDiagDetFactors
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_Iic_blockDiag_det_factors : ∀ (Φ : Type) [CommMonoid Φ] (p q : ℕ) (tW : Fin p → Φ) (tO : Fin q → Φ) (G : Fin (p + q) → Φ), (∀ (i : Fin (p + q)) (h : (i : ℕ) < p), G i = tW ⟨i, h⟩) → (∀ (i : Fin (p + q)) (h : p ≤ (i : ℕ)), G i = tO ⟨(i : ℕ) - p, by have := i.2; omega⟩) → ∀ i : Fin (p + q), (∀ h : (i : ℕ) < p, ∏ k ∈ Finset.Iic i, G k = ∏ l : Fin ((i : ℕ) + 1), tW (Fin.castLE h l)) ∧ (∀ h : p ≤ (i : ℕ), ∏ k ∈ Finset.Iic i, G k = (∏ l, tW l) * ∏ l : Fin ((i : ℕ) - p + 1), tO (Fin.castLE (by have := i.2; omega) l)) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.GradedLines.prod_first_graded_lines | exact GlobalTheory.CompanionTheory.Metric.GradedLines.prod_first_graded_lines | (intros; apply GlobalTheory.CompanionTheory.Metric.GradedLines.prod_first_graded_lines <;> assumption)
