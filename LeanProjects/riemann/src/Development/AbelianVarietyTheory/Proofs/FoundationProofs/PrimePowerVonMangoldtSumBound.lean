import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

open Finset ArithmeticFunction

namespace GlobalTheory

theorem prime_power_von_mangoldt_sum_bound : Formalism.HermitianLattices.GL2a2.SizeSpAll := by
  refine ⟨400, fun x hx p hp => ?_⟩
  unfold Formalism.HermitianLattices.GL2a2.sP
  have hx0 : (0 : ℝ) < x := by linarith
  have hz1 : (1 : ℝ) ≤ x ^ (400 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  set N : ℕ := ⌊x ^ (400 : ℝ)⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hz1)
  have hNz : (N : ℝ) ≤ x ^ (400 : ℝ) := Nat.floor_le (by linarith)
  have hp1 : 1 < p := hp.one_lt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hsub : (Icc 1 N).filter (fun i => p ^ i ≤ N) ⊆ Icc 1 (Nat.log p N) := by
    intro i hi
    simp only [mem_filter, mem_Icc] at hi ⊢
    exact ⟨hi.1.1, Nat.le_log_of_pow_le hp1 hi.2⟩
  have hcard : (((Icc 1 N).filter (fun i => p ^ i ≤ N)).card : ℝ) ≤ (Nat.log p N : ℝ) := by
    have := card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this
  have hterm : ∀ i ∈ (Icc 1 N).filter (fun i => p ^ i ≤ N),
      Formalism.HermitianLattices.GL2PrimeSums.cn x (p ^ i) ≤ Real.log p := by
    intro i hi
    simp only [mem_filter, mem_Icc] at hi
    unfold Formalism.HermitianLattices.GL2PrimeSums.cn
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    exact mul_le_of_le_one_right hlog (min_le_left _ _)
  have hpow : ((p : ℝ)) ^ (Nat.log p N) ≤ N := by
    exact_mod_cast Nat.pow_log_le_self p (by omega : N ≠ 0)
  calc ∑ i ∈ (Icc 1 N).filter (fun i => p ^ i ≤ N), Formalism.HermitianLattices.GL2PrimeSums.cn x (p ^ i)
      ≤ ((Icc 1 N).filter (fun i => p ^ i ≤ N)).card • Real.log p := sum_le_card_nsmul _ _ _ hterm
    _ = (((Icc 1 N).filter (fun i => p ^ i ≤ N)).card : ℝ) * Real.log p := nsmul_eq_mul _ _
    _ ≤ (Nat.log p N : ℝ) * Real.log p := mul_le_mul_of_nonneg_right hcard hlog
    _ = Real.log ((p : ℝ) ^ (Nat.log p N)) := (Real.log_pow _ _).symm
    _ ≤ Real.log (x ^ (400 : ℝ)) := Real.log_le_log (pow_pos hp0 _) (hpow.trans hNz)
    _ = 400 * Real.log x := Real.log_rpow hx0 _

end GlobalTheory
