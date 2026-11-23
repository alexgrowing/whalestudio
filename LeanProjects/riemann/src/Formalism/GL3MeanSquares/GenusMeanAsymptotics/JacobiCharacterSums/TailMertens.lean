import Mathlib

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_mertens_psi (N : ℕ) :
    ∑ n ∈ Icc 1 N, (Λ n : ℝ) ≤ (Real.log 4 + 4) * (N : ℝ) := by
  have h := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (Nat.cast_nonneg N)
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast] at h
  have hsub : ∑ n ∈ Icc 1 N, (Λ n : ℝ) = ∑ n ∈ Icc 0 N, (Λ n : ℝ) := by
    apply Finset.sum_subset
    · intro n hn
      simp only [mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      simp only [mem_Icc] at hn hn'
      have h0 : n = 0 := by omega
      subst h0
      simp
  rw [hsub]
  exact h

theorem tail_mertens_nat (N : ℕ) :
    ∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ) / (n : ℝ) ≤
      (∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ)) / ((N : ℝ) + 1)
        + (Real.log 4 + 4) * Real.log ((N : ℝ) + 1) := by
  have hc : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  induction N with
  | zero => simp
  | succ M ih =>
    have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
    have hM2 : (0:ℝ) < (M:ℝ) + 1 + 1 := by positivity
    have hB := tail_mertens_psi (M + 1)
    push_cast at hB
    have hlog : 1 / ((M:ℝ) + 1 + 1) ≤ Real.log ((M:ℝ) + 1 + 1) - Real.log ((M:ℝ) + 1) := by
      rw [← Real.log_div hM2.ne' hM1.ne']
      have h := Real.one_sub_inv_le_log_of_pos (x := ((M:ℝ) + 1 + 1) / ((M:ℝ) + 1)) (by positivity)
      calc 1 / ((M:ℝ) + 1 + 1) = 1 - (((M:ℝ) + 1 + 1) / ((M:ℝ) + 1))⁻¹ := by
            field_simp
            ring
        _ ≤ _ := h
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 + 1 by omega)]
    push_cast
    set B := ∑ n ∈ Icc 1 (M + 1), (Λ n : ℝ) with hBdef
    set L := (Λ (M + 1 + 1) : ℝ) with hLdef
    have key1 : B / ((M:ℝ) + 1) ≤ (B + (Real.log 4 + 4)) / ((M:ℝ) + 1 + 1) := by
      rw [div_le_div_iff₀ hM1 hM2]
      nlinarith
    have key2 : (Real.log 4 + 4) / ((M:ℝ) + 1 + 1) ≤
        (Real.log 4 + 4) * (Real.log ((M:ℝ) + 1 + 1) - Real.log ((M:ℝ) + 1)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hlog hc
    rw [add_div] at key1 ⊢
    linarith

theorem tail_mertens : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 2 ≤ y →
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ C * Real.log y := by
  have hc : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 4 + 4) * (1 / Real.log 2 + 1),
    mul_nonneg hc (add_nonneg (one_div_nonneg.2 hl2.le) zero_le_one), ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  obtain ⟨M, hM⟩ : ∃ M, ⌊y⌋₊ = M + 1 :=
    ⟨⌊y⌋₊ - 1, by
      have : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega⟩
  rw [hM]
  have h1 := tail_mertens_nat M
  have hpsi := tail_mertens_psi (M + 1)
  push_cast at hpsi
  have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
  have hMy : (M:ℝ) + 1 ≤ y := by
    have := Nat.floor_le hy0
    rw [hM] at this
    push_cast at this
    exact this
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlogM : Real.log ((M:ℝ) + 1) ≤ Real.log y := Real.log_le_log hM1 hMy
  have hq : (∑ n ∈ Icc 1 (M + 1), (Λ n : ℝ)) / ((M:ℝ) + 1) ≤ Real.log 4 + 4 := by
    rw [div_le_iff₀ hM1]
    exact hpsi
  have hone : 1 ≤ Real.log y / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    linarith
  calc _ ≤ (Real.log 4 + 4) + (Real.log 4 + 4) * Real.log y := by
        have := mul_le_mul_of_nonneg_left hlogM hc
        linarith
    _ ≤ (Real.log 4 + 4) * (Real.log y / Real.log 2) + (Real.log 4 + 4) * Real.log y := by
        have := mul_le_mul_of_nonneg_left hone hc
        linarith
    _ = (Real.log 4 + 4) * (1 / Real.log 2 + 1) * Real.log y := by
        field_simp

end Formalism.HermitianLattices.Ext.BoxTail
