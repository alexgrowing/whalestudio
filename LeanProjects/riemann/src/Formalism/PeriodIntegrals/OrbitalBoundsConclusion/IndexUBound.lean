import Mathlib
import Formalism.PeriodIntegrals.IndexUBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IndexUpperBound.OneSubSumLeProd

theorem product_lowerBound : PI.IndexUBound.IndexUBound := by
  classical
  intro ι S g r y hg hy
  have h2 : ∀ v ∈ S, (2 : ℝ) ≤ g v := fun v hv => by exact_mod_cast hg v hv

  have hfac : ∀ v ∈ S, ∏ i ∈ Finset.Ico 1 r, ((g v : ℝ) ^ i - 1) =
      (g v : ℝ) ^ (r * (r - 1) / 2) * ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i) :=
    fun v hv => PI.UnitaryGroupMassFormula.IndexUBound.prod_factor _ (by linarith [h2 v hv] : (0 : ℝ) < g v).ne' r
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]

  have hQ := PI.UnitaryGroupMassFormula.IndexUBound.one_sub_sum_le_prod S
    (fun v => ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i)) (fun v => 1 / ((g v : ℝ) - 1))
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).1)
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).2.1)
    (fun v hv => div_nonneg zero_le_one (by linarith [h2 v hv]))
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).2.2)
  beta_reduce at hQ
  have hpos : 0 ≤ ∏ v ∈ S, (g v : ℝ) ^ (r * (r - 1) / 2) :=
    Finset.prod_nonneg fun v _ => by positivity
  have key := mul_le_mul_of_nonneg_right
    (show 1 - y ≤ ∏ v ∈ S, ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i) by linarith) hpos
  linarith
