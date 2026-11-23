import Mathlib

open Finset Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem rootSum (N : ℕ) (hN : 0 < N) (t : ℕ) (ht : t < N) :
    ∑ k ∈ range N, (cexp (2 * Real.pi * I / N) ^ k) ^ t = if t = 0 then (N : ℂ) else 0 := by

  have hprim := Complex.isPrimitiveRoot_exp N (by omega)
  split_ifs with ht0
  · subst ht0
    simp
  · have hx : cexp (2 * Real.pi * I / N) ^ t ≠ 1 := hprim.pow_ne_one_of_pos_of_lt (by omega) ht
    have h1 : ∀ k, (cexp (2 * Real.pi * I / N) ^ k) ^ t = (cexp (2 * Real.pi * I / N) ^ t) ^ k := fun k => pow_right_comm _ _ _
    simp_rw [h1]
    have hxN : (cexp (2 * Real.pi * I / N) ^ t) ^ N = 1 := by rw [pow_right_comm, hprim.pow_eq_one, one_pow]
    rw [geom_sum_eq hx, hxN, sub_self, zero_div]

theorem rootNorm (N : ℕ) (_hN : 0 < N) (k : ℕ) : ‖cexp (2 * Real.pi * I / N) ^ k‖ = 1 := by

  rw [norm_pow, (Complex.isPrimitiveRoot_exp N (by omega)).norm'_eq_one (by omega), one_pow]

theorem rootPowN (N : ℕ) (hN : 0 < N) (k : ℕ) : (cexp (2 * Real.pi * I / N) ^ k) ^ N = 1 := by

  rw [pow_right_comm, (Complex.isPrimitiveRoot_exp N (by omega)).pow_eq_one, one_pow]

theorem rootAvg (N : ℕ) (j : ℕ) (hj : 1 ≤ j) (hjN : j < N) (y : ℂ) (hy : ‖y‖ ≠ 1) :
    ∑ k ∈ range N, (y * cexp (2 * Real.pi * I / N) ^ k) ^ j / (1 - y * cexp (2 * Real.pi * I / N) ^ k)
      = N * (y ^ N / (1 - y ^ N)) := by

  have hN : 0 < N := by omega
  have hyN : 1 - y ^ N ≠ 0 := by
    intro h
    have h2 : y ^ N = 1 := by linear_combination -h
    have h3 : ‖y‖ ^ N = 1 := by rw [← norm_pow, h2, norm_one]
    exact hy ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h3)
  have hxk : ∀ k, 1 - y * cexp (2 * Real.pi * I / N) ^ k ≠ 0 := by
    intro k h
    have h2 : y * cexp (2 * Real.pi * I / N) ^ k = 1 := by linear_combination -h
    apply hy
    have h3 := congrArg norm h2
    rwa [norm_mul, rootNorm N hN k, mul_one, norm_one] at h3
  have hS : ∀ s : ℕ, ∑ k ∈ range N, (cexp (2 * Real.pi * I / N) ^ k) ^ s = if s % N = 0 then (N : ℂ) else 0 := by
    intro s
    have h1 : ∀ k, (cexp (2 * Real.pi * I / N) ^ k) ^ s = (cexp (2 * Real.pi * I / N) ^ k) ^ (s % N) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod s N, pow_add, pow_mul, rootPowN N hN k, one_pow, one_mul]
    simp_rw [h1]
    rw [rootSum N hN _ (Nat.mod_lt _ hN)]
  have hterm : ∀ k, (y * cexp (2 * Real.pi * I / N) ^ k) ^ j / (1 - y * cexp (2 * Real.pi * I / N) ^ k) =
      (∑ m ∈ range N, y ^ (j + m) * (cexp (2 * Real.pi * I / N) ^ k) ^ (j + m)) / (1 - y ^ N) := by
    intro k
    rw [div_eq_div_iff (hxk k) hyN]
    have hg := mul_neg_geom_sum (y * cexp (2 * Real.pi * I / N) ^ k) N
    have hxN : (y * cexp (2 * Real.pi * I / N) ^ k) ^ N = y ^ N := by rw [mul_pow, rootPowN N hN k, mul_one]
    rw [hxN] at hg
    have h1 : ∑ m ∈ range N, y ^ (j + m) * (cexp (2 * Real.pi * I / N) ^ k) ^ (j + m) =
        (y * cexp (2 * Real.pi * I / N) ^ k) ^ j * ∑ i ∈ range N, (y * cexp (2 * Real.pi * I / N) ^ k) ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [h1, ← hg]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hS]
  rw [Finset.sum_eq_single (N - j)]
  · rw [if_pos (by rw [Nat.add_sub_cancel' hjN.le, Nat.mod_self]), Nat.add_sub_cancel' hjN.le]
    ring
  · intro m hm hne
    rw [Finset.mem_range] at hm
    rw [if_neg, mul_zero]
    by_cases hlt : j + m < N
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · intro h
    exfalso
    simp at h
    omega

theorem ratioLim (y : ℂ) (hy : ‖y‖ ≠ 1) :
    Tendsto (fun N : ℕ => y ^ N / (1 - y ^ N)) atTop (𝓝 (if 1 < ‖y‖ then (-1 : ℂ) else 0)) := by

  split_ifs with h
  · have hz : ‖y⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ h
    have h1 := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
    have h2 : Tendsto (fun N : ℕ => 1 / (y⁻¹ ^ N - 1)) atTop (𝓝 (1 / (0 - 1))) :=
      tendsto_const_nhds.div (h1.sub tendsto_const_nhds) (by norm_num)
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      linarith
    have h3 : (fun N : ℕ => y ^ N / (1 - y ^ N)) = (fun N : ℕ => 1 / (y⁻¹ ^ N - 1)) := by
      funext N
      have hyN : y ^ N ≠ 0 := pow_ne_zero _ hy0
      rw [inv_pow, show (y ^ N)⁻¹ - 1 = (1 - y ^ N) / y ^ N by field_simp, one_div_div]
    have h4 : (-1 : ℂ) = 1 / (0 - 1) := by norm_num
    rw [h3, h4]
    exact h2
  · have hlt : ‖y‖ < 1 := lt_of_le_of_ne (not_lt.mp h) hy
    have h1 := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
    have h2 : Tendsto (fun N : ℕ => y ^ N / (1 - y ^ N)) atTop (𝓝 (0 / (1 - 0))) :=
      h1.div (tendsto_const_nhds.sub h1) (by norm_num)
    rw [show (0 : ℂ) / (1 - 0) = 0 by norm_num] at h2
    exact h2

theorem avgLimit {n : ℕ} (y : Fin n → ℂ) (hy : ∀ i, ‖y i‖ ≠ 1) (j : ℕ) (hj : 1 ≤ j) (K : ℝ)
    (hK : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖∑ i, (y i * ζ) ^ j / (1 - y i * ζ)‖ ≤ K) :
    ((univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) ≤ K := by

  classical
  have hbound : ∀ N : ℕ, j < N → ‖∑ i, y i ^ N / (1 - y i ^ N)‖ ≤ K := by
    intro N hjN
    have hN : 0 < N := by omega
    have h1 : ∑ k ∈ range N, ∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
        (1 - y i * cexp (2 * Real.pi * I / N) ^ k) = N * ∑ i, y i ^ N / (1 - y i ^ N) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => rootAvg N j hj hjN (y i) (hy i))
    have h2 : ‖∑ k ∈ range N, ∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
        (1 - y i * cexp (2 * Real.pi * I / N) ^ k)‖ ≤ N * K := by
      calc _ ≤ ∑ k ∈ range N, ‖∑ i, (y i * cexp (2 * Real.pi * I / N) ^ k) ^ j /
            (1 - y i * cexp (2 * Real.pi * I / N) ^ k)‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ range N, K := Finset.sum_le_sum (fun k _ => hK _ (rootNorm N hN k))
        _ = N * K := by simp
    rw [h1, norm_mul, Complex.norm_natCast] at h2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    exact le_of_mul_le_mul_left h2 hNpos
  have hlim : Tendsto (fun N : ℕ => ∑ i, y i ^ N / (1 - y i ^ N)) atTop
      (𝓝 (∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0)) :=
    tendsto_finset_sum _ (fun i _ => ratioLim (y i) (hy i))
  have hle : ‖∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0‖ ≤ K := by
    apply le_of_tendsto hlim.norm
    rw [Filter.eventually_atTop]
    exact ⟨j + 1, fun N hN => hbound N (by omega)⟩
  have hval : ‖∑ i, if 1 < ‖y i‖ then (-1 : ℂ) else 0‖ = ((univ.filter (fun i => 1 < ‖y i‖)).card : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, norm_mul, norm_neg,
      norm_one, mul_one, Complex.norm_natCast]
  rw [← hval]
  exact hle

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
