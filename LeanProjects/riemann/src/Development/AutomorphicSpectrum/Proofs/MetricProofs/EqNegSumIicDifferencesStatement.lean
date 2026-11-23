import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EqNegSumIicDifferences
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_neg_sum_Iic_differences : ∀ (N : ℕ) (M : Type) [AddCommGroup M] (f : Fin N → M) (i : Fin N), f i = -∑ k ∈ Finset.Iic i, (if h : (k : ℕ) = 0 then -f k else f ⟨(k : ℕ) - 1, by have := k.2; omega⟩ - f k) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.Telescope.fin_iic_telescope | exact GlobalTheory.CompanionTheory.Metric.Telescope.fin_iic_telescope | (intros; apply GlobalTheory.CompanionTheory.Metric.Telescope.fin_iic_telescope <;> assumption)
