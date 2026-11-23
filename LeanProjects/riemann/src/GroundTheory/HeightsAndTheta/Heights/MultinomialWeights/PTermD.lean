import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset Filter Topology

theorem termD_term_le {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) ≤ 2 * (Real.log p / p) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp0 : (0 : ℝ) < p := by linarith
  rw [mul_div_assoc', div_le_div_iff₀ hden hp0]
  nlinarith [mul_nonneg hlog (by nlinarith : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 2)]

theorem TermD.proof : TermD.Statement := by
  intro C7 hC7
  refine ⟨2 + C7 / Real.log 2, ?_⟩
  intro d S B0 A0 hB0 h7 hA
  obtain ⟨hlow, -⟩ := h7 A0 hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB0r : (2 : ℝ) ≤ B0 := by exact_mod_cast hB0
  have hlogB : Real.log 2 ≤ Real.log B0 := Real.log_le_log (by norm_num) hB0r
  have hC7le : C7 ≤ C7 / Real.log 2 * Real.log B0 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hlogB hC7
  have hsum : ∑ p ∈ S.level.primeFactors.filter (fun p => B0 < p),
        (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) ≤
      2 * ∑ p ∈ S.level.primeFactors, Real.log p / (p : ℝ) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ p ∈ S.level.primeFactors.filter (fun p => B0 < p), 2 * (Real.log p / p) :=
          Finset.sum_le_sum fun p hp =>
            termD_term_le (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).two_le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => mul_nonneg zero_le_two
            (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)))
  have hS0 : 0 ≤ ∑ p ∈ S.level.primeFactors, Real.log p / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hlogB0 : 0 ≤ Real.log B0 := le_trans hl2.le hlogB
  have hCpos : 0 ≤ C7 / Real.log 2 := div_nonneg hC7 hl2.le
  nlinarith [mul_nonneg hCpos hS0]

end GroundTheory.Heights₂.Heights.TheoremB
