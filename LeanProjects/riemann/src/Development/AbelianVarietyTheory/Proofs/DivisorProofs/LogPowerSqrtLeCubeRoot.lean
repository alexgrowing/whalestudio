import Mathlib

open Filter Topology Real

namespace GlobalTheory

theorem small_t_log_power_bound : ∀ (A B μ K : ℝ), 0 ≤ A → 0 ≤ B → 0 ≤ μ → 0 ≤ K → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
    A * (Real.log (1 / t) + B) ^ μ * t ^ ((1 : ℝ) / 2) + K * t ^ 2 ≤ t ^ ((1 : ℝ) / 3) := by
  intro A B μ K hA hB hμ hK

  have h1 : Tendsto (fun t : ℝ => A * exp (B / 6) *
      ((-Real.log t + B) ^ μ * exp (-(1 / 6) * (-Real.log t + B)))) (𝓝[>] 0) (𝓝 0) := by
    have hu : Tendsto (fun t : ℝ => -Real.log t + B) (𝓝[>] 0) atTop :=
      tendsto_atTop_add_const_right _ B (tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero)
    have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero μ (1 / 6) (by norm_num)).comp hu
    simpa using this.const_mul (A * exp (B / 6))
  have h2 : Tendsto (fun t : ℝ => K * t ^ ((5 : ℝ) / 3)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => t ^ ((5 : ℝ) / 3)) (𝓝 0) (𝓝 ((0 : ℝ) ^ ((5 : ℝ) / 3))) :=
      Real.continuousAt_rpow_const 0 ((5 : ℝ) / 3) (Or.inr (by norm_num))
    rw [Real.zero_rpow (by norm_num)] at hc
    simpa using (hc.mono_left nhdsWithin_le_nhds).const_mul K
  have e1 := h1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have e2 := h2.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have e := e1.and e2
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset] at e
  obtain ⟨u, hu, hsub⟩ := e
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨u / 2, by positivity, fun t ht htu => ?_⟩
  have htmem : t ∈ Set.Ioo (0 : ℝ) u := ⟨ht, by linarith⟩
  obtain ⟨b1, b2⟩ := hsub htmem
  have hlog : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
  have key : A * (Real.log (1 / t) + B) ^ μ * t ^ ((1 : ℝ) / 6) = A * exp (B / 6) *
      ((-Real.log t + B) ^ μ * exp (-(1 / 6) * (-Real.log t + B))) := by
    rw [hlog, Real.rpow_def_of_pos ht]
    have : exp (Real.log t * (1 / 6)) = exp (B / 6) * exp (-(1 / 6) * (-Real.log t + B)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  have s1 : t ^ ((1 : ℝ) / 2) = t ^ ((1 : ℝ) / 6) * t ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add ht]; norm_num
  have s2 : t ^ 2 = t ^ ((5 : ℝ) / 3) * t ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add ht, ← Real.rpow_natCast]; norm_num
  have hp : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
  calc A * (Real.log (1 / t) + B) ^ μ * t ^ ((1 : ℝ) / 2) + K * t ^ 2
      = (A * (Real.log (1 / t) + B) ^ μ * t ^ ((1 : ℝ) / 6)) * t ^ ((1 : ℝ) / 3)
        + (K * t ^ ((5 : ℝ) / 3)) * t ^ ((1 : ℝ) / 3) := by rw [s1, s2]; ring
    _ ≤ (1 / 2) * t ^ ((1 : ℝ) / 3) + (1 / 2) * t ^ ((1 : ℝ) / 3) := by
        rw [key]
        exact add_le_add (mul_le_mul_of_nonneg_right b1 hp) (mul_le_mul_of_nonneg_right b2 hp)
    _ = t ^ ((1 : ℝ) / 3) := by ring

end GlobalTheory
