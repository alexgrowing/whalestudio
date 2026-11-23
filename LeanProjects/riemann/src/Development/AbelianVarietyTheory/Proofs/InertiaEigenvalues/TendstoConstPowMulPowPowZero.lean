import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory

theorem tendsto_const_pow_mul_pow_pow_zero : ∀ (C r : ℝ) (l : ℕ), 0 ≤ C → 0 ≤ r → r < 1 → 2 ≤ l →
    Tendsto (fun n : ℕ => C ^ n * r ^ (l ^ n)) atTop (𝓝 0) := by
  intro C r l hC hr hr1 hl
  have h1 : Tendsto (fun m : ℕ => C * r ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul C
  obtain ⟨m, hm⟩ := (h1.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))).exists
  have h2 : ∀ᶠ n : ℕ in atTop, m * n ≤ l ^ n := by
    have ht := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ) < 2)).const_mul (m:ℝ)
    rw [mul_zero] at ht
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn
    have h2pos : (0:ℝ) < 2 ^ n := by positivity
    rw [pow_one, ← mul_div_assoc, div_lt_one h2pos] at hn
    have h3 : m * n ≤ 2 ^ n := by exact_mod_cast hn.le
    exact h3.trans (Nat.pow_le_pow_left hl n)
  have hbound : ∀ᶠ n : ℕ in atTop, C ^ n * r ^ (l ^ n) ≤ (1/2 : ℝ) ^ n := by
    filter_upwards [h2] with n hn
    calc C ^ n * r ^ (l ^ n) ≤ C ^ n * r ^ (m * n) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr hr1.le hn) (pow_nonneg hC n)
      _ = (C * r ^ m) ^ n := by rw [mul_pow, ← pow_mul]
      _ ≤ (1/2) ^ n := pow_le_pow_left₀ (by positivity) hm.le n
  exact squeeze_zero' (Eventually.of_forall fun n => by positivity) hbound
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

end GlobalTheory
