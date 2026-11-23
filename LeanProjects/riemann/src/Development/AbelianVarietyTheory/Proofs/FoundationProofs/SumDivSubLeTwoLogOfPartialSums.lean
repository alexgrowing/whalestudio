import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

open Finset ArithmeticFunction

namespace GlobalTheory

theorem sum_div_sub_le_two_log_of_partial_sums (a : ℕ → ℝ)
    (h : ∀ N : ℕ, ∑ n ∈ Icc 1 N, a n ≤ 2 * (N : ℝ)) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n / (n : ℝ) - (∑ n ∈ Icc 1 N, a n) / ((N : ℝ) + 1)
      ≤ 2 * Real.log ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN := h (N + 1)
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)] at hN
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    push_cast at hN ⊢
    set P := ∑ n ∈ Icc 1 N, a n
    set S := ∑ n ∈ Icc 1 N, a n / (n : ℝ)
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    have h2 : (0 : ℝ) < (N : ℝ) + 1 + 1 := by linarith
    have hlog : 1 / ((N : ℝ) + 1 + 1) ≤ Real.log ((N : ℝ) + 1 + 1) - Real.log ((N : ℝ) + 1) := by
      have := Real.log_le_sub_one_of_pos (div_pos h1 h2)
      rw [Real.log_div h1.ne' h2.ne'] at this
      have e : ((N : ℝ) + 1) / ((N : ℝ) + 1 + 1) - 1 = -(1 / ((N : ℝ) + 1 + 1)) := by
        field_simp; ring
      linarith
    have e : S + a (N + 1) / ((N : ℝ) + 1) - (P + a (N + 1)) / ((N : ℝ) + 1 + 1)
        = (S - P / ((N : ℝ) + 1)) + ((P + a (N + 1)) / ((N : ℝ) + 1)) * (1 / ((N : ℝ) + 1 + 1)) := by
      field_simp; ring
    have h3 : (P + a (N + 1)) / ((N : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ h1]; linarith
    have h4 : ((P + a (N + 1)) / ((N : ℝ) + 1)) * (1 / ((N : ℝ) + 1 + 1))
        ≤ 2 * (1 / ((N : ℝ) + 1 + 1)) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    rw [e]
    linarith

theorem chebyshev_coefficient_sum_bound : Formalism.HermitianLattices.GL2a2.SizeSumC := by
  intro hψ
  refine ⟨806, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h : ∀ N : ℕ, ∑ n ∈ Icc 1 N, (Λ n : ℝ) ≤ 2 * (N : ℝ) := fun N => by
    simpa using hψ N (Nat.cast_nonneg N)
  set N := ⌊x ^ (400 : ℝ)⌋₊ with hNdef
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hA := sum_div_sub_le_two_log_of_partial_sums (fun n => (Λ n : ℝ)) h N
  have hB : (∑ n ∈ Icc 1 N, (Λ n : ℝ)) / ((N : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ h1]; linarith [h N]
  have hz1 : 1 ≤ x ^ (400 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hNz : (N : ℝ) ≤ x ^ (400 : ℝ) := Nat.floor_le (by linarith)
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hl2' := Real.log_two_gt_d9
  have hC : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + 400 * Real.log x := by
    have : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * x ^ (400 : ℝ)) :=
      Real.log_le_log h1 (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith), Real.log_rpow hx0] at this
    exact this
  have hD : ∑ n ∈ Icc 1 N, (Λ n : ℝ) / (n : ℝ) ≤ 806 * Real.log x := by
    linarith
  calc ∑ n ∈ Icc 1 N, Formalism.HermitianLattices.GL2PrimeSums.cn x n
      ≤ ∑ n ∈ Icc 1 N, x * ((Λ n : ℝ) / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        unfold Formalism.HermitianLattices.GL2PrimeSums.cn
        calc (Λ n : ℝ) * min 1 (x / (n : ℝ)) ≤ (Λ n : ℝ) * (x / (n : ℝ)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) vonMangoldt_nonneg
          _ = x * ((Λ n : ℝ) / (n : ℝ)) := by ring
    _ = x * ∑ n ∈ Icc 1 N, (Λ n : ℝ) / (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ x * (806 * Real.log x) := mul_le_mul_of_nonneg_left hD hx0.le
    _ = 806 * x * Real.log x := by ring

end GlobalTheory
