import Mathlib

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_num_rpow (x ε : ℝ) (hx : 0 < x) :
    (x ^ 400) ^ (1 - 1 / 400 + ε / 1600 : ℝ) = x ^ 399 * x ^ (ε / 4) := by
  rw [← Real.rpow_natCast x 400, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x 399,
    ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

theorem tail_num_alg (x Q K l a g : ℝ) (hx : 0 < x) (hQ : 0 < Q) :
    x * ((K * l * (l * (1 / x ^ 2) * (x ^ 399 * a) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * g / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2)))
      = K * l ^ 2 * a + K * (l * x ^ 403 / Q) + (x ^ 398 + 1) * g / x ^ 399 := by
  have hx0 : x ≠ 0 := hx.ne'
  have hQ0 : Q ≠ 0 := hQ.ne'
  field_simp

theorem tail_num_third (x : ℝ) (hx : 3 ≤ x) :
    (x ^ 398 + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 399 ≤ 802 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hp : 0 < x ^ 398 := by positivity
  have hp1 : 1 ≤ x ^ 398 := one_le_pow₀ hx1
  have hA : x ^ 400 + x ^ 400 * (1 / x ^ 2) = x ^ 398 * (x ^ 2 + 1) := by
    field_simp
  have hsq : x ^ 2 + 1 ≤ x ^ 3 := by nlinarith
  have hA1 : x ^ 398 * (x ^ 2 + 1) ≤ x ^ 401 := by
    have : x ^ 401 = x ^ 398 * x ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsq hp.le
  have hApos : 0 < x ^ 398 * (x ^ 2 + 1) := by positivity
  have hAge : 1 ≤ x ^ 398 * (x ^ 2 + 1) := by nlinarith
  have hL0 : 0 ≤ Real.log (x ^ 398 * (x ^ 2 + 1)) := Real.log_nonneg hAge
  have hL1 : Real.log (x ^ 398 * (x ^ 2 + 1)) ≤ 401 * x := by
    calc Real.log (x ^ 398 * (x ^ 2 + 1)) ≤ Real.log (x ^ 401) := Real.log_le_log hApos hA1
      _ = 401 * Real.log x := by rw [Real.log_pow]; norm_num
      _ ≤ 401 * x := by
        have := Real.log_le_sub_one_of_pos hx0
        linarith
  have hx399 : x ≤ x ^ 399 := by
    have : x ^ 399 = x * x ^ 398 := by ring
    rw [this]
    nlinarith
  rw [hA, div_le_iff₀ (by positivity : (0:ℝ) < x ^ 399)]
  calc (x ^ 398 + 1) * Real.log (x ^ 398 * (x ^ 2 + 1))
      ≤ (x ^ 398 + 1) * (401 * x) := mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = 401 * x ^ 399 + 401 * x := by ring
    _ ≤ 802 * x ^ 399 := by linarith

theorem tail_num_exp (ε K : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop, K * (x ^ 404 * Real.exp (-(x ^ (ε / 6)))) ≤ 1 / 3 := by
  have hs : 0 < ε / 6 := by positivity
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ (ε / 6)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hs
  have h2 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (404 / (ε / 6)) 1 one_pos).comp h1
  have hc : ε / 6 * (404 / (ε / 6)) = (404 : ℝ) := by field_simp
  have h3 : Filter.Tendsto (fun x : ℝ => x ^ 404 * Real.exp (-(x ^ (ε / 6))))
      Filter.atTop (nhds 0) := by
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    simp only [Function.comp, neg_mul, one_mul]
    rw [← Real.rpow_mul hx.le, hc]
    congr 1
    exact_mod_cast Real.rpow_natCast x 404
  have h4 : Filter.Tendsto (fun x : ℝ => K * (x ^ 404 * Real.exp (-(x ^ (ε / 6)))))
      Filter.atTop (nhds 0) := by
    simpa using h3.const_mul K
  exact h4.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))

theorem tail_num (ε K : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 0 ≤ K) : ∃ x₀ : ℝ, 3 ≤ x₀ ∧
    ∀ x Q : ℝ, x₀ ≤ x → 0 < Q → x ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (ε / 4) →
      x * ((K * Real.log Q * (Real.log Q * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + ε / 1600) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ x ^ ε := by
  have hq : 0 < ε / 4 := by positivity
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      K * (x ^ 404 * Real.exp (-(x ^ (ε / 6)))) ≤ 1 / 3 ∧ K + 803 ≤ x ^ (ε / 4) :=
    (tail_num_exp ε K hε).and
      ((tendsto_rpow_atTop hq).eventually (Filter.eventually_ge_atTop (K + 803)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max N 3, le_max_right _ _, ?_⟩
  intro x Q hx hQ hlo hhi
  have hxN : N ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hexp, hy⟩ := hN x hxN
  rw [tail_num_rpow x ε hx0, tail_num_alg x Q K (Real.log Q) (x ^ (ε / 4))
    (Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2))) hx0 hQ]
  set y := x ^ (ε / 4) with hydef
  set l := Real.log Q with hldef
  have hs0 : 0 < x ^ (ε / 6) := Real.rpow_pos_of_pos hx0 _
  have hl0 : 0 ≤ l := by linarith
  have hy0 : 0 ≤ y := by linarith
  have ht1 : K * l ^ 2 * y ≤ K * y ^ 3 := by
    have : l ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hl0 hhi 2
    have h' : l ^ 2 * y ≤ y ^ 2 * y := mul_le_mul_of_nonneg_right this hy0
    calc K * l ^ 2 * y = K * (l ^ 2 * y) := by ring
      _ ≤ K * (y ^ 2 * y) := mul_le_mul_of_nonneg_left h' hK
      _ = K * y ^ 3 := by ring
  have hyx : y ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : ε / 4 ≤ 1)
    rwa [Real.rpow_one] at this
  have hlx : l ≤ x := le_trans hhi hyx
  have hQinv : 1 / Q ≤ Real.exp (-(x ^ (ε / 6))) := by
    have hQe : Real.exp (x ^ (ε / 6)) ≤ Q := by
      calc Real.exp (x ^ (ε / 6)) ≤ Real.exp l := Real.exp_le_exp.2 hlo
        _ = Q := Real.exp_log hQ
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hQe
  have ht2 : K * (l * x ^ 403 / Q) ≤ 1 / 3 := by
    have hin : l * x ^ 403 / Q ≤ x ^ 404 * Real.exp (-(x ^ (ε / 6))) := by
      calc l * x ^ 403 / Q = (l * x ^ 403) * (1 / Q) := by ring
        _ ≤ (x * x ^ 403) * Real.exp (-(x ^ (ε / 6))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hlx (by positivity)) hQinv
            (by positivity) (by positivity)
        _ = x ^ 404 * Real.exp (-(x ^ (ε / 6))) := by ring
    exact le_trans (mul_le_mul_of_nonneg_left hin hK) hexp
  have ht3 := tail_num_third x hx3
  have hpow : x ^ ε = y * y * y * y := by
    rw [hydef, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  have hy1 : 803 ≤ y := by linarith
  have hy3 : y ≤ y ^ 3 := by nlinarith
  have hfin : K * y ^ 3 + 1 / 3 + 802 ≤ y * y * y * y := by
    have : (K + 803) * y ^ 3 ≤ y * y ^ 3 :=
      mul_le_mul_of_nonneg_right hy (by positivity)
    nlinarith
  rw [hpow]
  linarith

end Formalism.HermitianLattices.Ext.BoxTail
