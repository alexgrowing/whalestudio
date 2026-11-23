import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StMonicRootGrowth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Finset

theorem norm_eval_le_sum_norm_coeff_mul {d : ℕ} (a : MvPolynomial (Fin d) ℂ) (y : Fin d → ℂ) :
    ‖eval y a‖ ≤ (∑ s ∈ a.support, ‖coeff s a‖) * (1 + ‖y‖) ^ a.totalDegree := by
  have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  rw [eval_eq, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun s hs ↦ ?_)
  rw [norm_mul, norm_prod]
  gcongr
  calc ∏ i ∈ s.support, ‖y i ^ s i‖
      ≤ ∏ i ∈ s.support, (1 + ‖y‖) ^ s i := by
        gcongr with i
        rw [norm_pow]
        gcongr
        exact (norm_le_pi_norm y i).trans (le_add_of_nonneg_left zero_le_one)
    _ = (1 + ‖y‖) ^ (s.sum fun _ e ↦ e) := prod_pow_eq_pow_sum _ _ _
    _ ≤ (1 + ‖y‖) ^ a.totalDegree := pow_le_pow_right₀ h1 (le_totalDegree hs)

theorem norm_le_one_add_sum_norm_coeff_of_monic {q : Polynomial ℂ} (hq : q.Monic) {τ : ℂ}
    (hτ : q.IsRoot τ) : ‖τ‖ ≤ 1 + ∑ i ∈ range q.natDegree, ‖q.coeff i‖ := by
  have key := hτ.norm_lt_cauchyBound hq.ne_zero
  have hs : Polynomial.cauchyBound q ≤ (∑ i ∈ range q.natDegree, ‖q.coeff i‖₊) + 1 := by
    unfold Polynomial.cauchyBound
    rw [hq.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun i hi ↦ single_le_sum (f := fun i ↦ ‖q.coeff i‖₊) (fun _ _ ↦ by positivity) hi
  have h' : ((‖τ‖₊ : NNReal) : ℝ) ≤ (((∑ i ∈ range q.natDegree, ‖q.coeff i‖₊) + 1 : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr (key.trans_le hs).le
  push_cast at h'
  linarith

theorem MonicRootGrowth.proof : MonicRootGrowth.Statement := by
  intro d m hm
  set n := m.natDegree
  set S : ℕ → ℝ := fun i ↦ ∑ s ∈ (m.coeff i).support, ‖coeff s (m.coeff i)‖
  refine ⟨1 + ∑ i ∈ range n, S i, (range n).sup fun i ↦ (m.coeff i).totalDegree, fun y τ hτ ↦ ?_⟩
  have hmap : (m.map (eval y)).Monic := hm.map _
  have hdeg : (m.map (eval y)).natDegree = n := hm.natDegree_map _
  have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  set M := (range n).sup fun i ↦ (m.coeff i).totalDegree
  have hM : (1 : ℝ) ≤ (1 + ‖y‖) ^ M := one_le_pow₀ h1
  have hb := norm_le_one_add_sum_norm_coeff_of_monic hmap hτ
  rw [hdeg] at hb
  simp only [Polynomial.coeff_map] at hb
  calc ‖τ‖ ≤ 1 + ∑ i ∈ range n, ‖eval y (m.coeff i)‖ := hb
    _ ≤ 1 * (1 + ‖y‖) ^ M + ∑ i ∈ range n, S i * (1 + ‖y‖) ^ M := by
        gcongr with i hi
        · simpa using hM
        · refine (norm_eval_le_sum_norm_coeff_mul _ y).trans ?_
          gcongr
          exact le_sup (f := fun i ↦ (m.coeff i).totalDegree) hi
    _ = (1 + ∑ i ∈ range n, S i) * (1 + ‖y‖) ^ M := by rw [add_mul, sum_mul]

end GroundTheory.Heights₂.Heights.HilbertSamuel
