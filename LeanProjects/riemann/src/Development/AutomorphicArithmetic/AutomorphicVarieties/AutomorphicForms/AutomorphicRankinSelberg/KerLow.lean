import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

noncomputable section

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

theorem kerLow : KerLow := by
  intro s hs x z hz
  obtain ⟨hs1, hs2⟩ := hs
  unfold ker
  have hy : 0 < z.im := z.im_pos
  have hy2 : 3 ≤ 4 * z.im ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  set r : ℝ := ‖(z : ℂ)‖ with hr
  set n : ℝ := ‖x‖ with hn
  have hr0 : 0 ≤ r := norm_nonneg _
  have hn0 : 0 ≤ n := norm_nonneg _
  have hyr : z.im ≤ r := by
    have := Complex.abs_im_le_norm (z : ℂ)
    simp only [UpperHalfPlane.coe_im] at this
    exact le_trans (le_abs_self _) this
  by_cases hx0 : x = 0
  · subst hx0
    have hn' : n = 0 := by simp [hn]
    have hs0 : -(2 * s) ≠ 0 := by linarith
    rw [hn', Real.zero_rpow hs0, mul_zero]
    exact Real.rpow_nonneg (div_nonneg hy.le (Complex.normSq_nonneg _)) _
  have hxi : ∀ i, |((x i : ℤ) : ℝ)| ≤ n := by
    intro i
    have := norm_le_pi_norm x i
    rwa [Int.norm_eq_abs] at this
  have hn1 : 1 ≤ n := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    have h1 : (1 : ℝ) ≤ |((x i : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hi
    exact h1.trans (hxi i)
  set w : ℂ := (x 0 : ℂ) * (z : ℂ) + (x 1 : ℂ) with hw
  have hwle : ‖w‖ ≤ n * (r + 1) := by
    calc ‖w‖ ≤ ‖(x 0 : ℂ)‖ * r + ‖(x 1 : ℂ)‖ := by
          rw [hw]
          exact (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ n * r + n := by
          rw [Complex.norm_intCast, Complex.norm_intCast]
          have := hxi 0
          have := hxi 1
          nlinarith
      _ = n * (r + 1) := by ring
  have hwne : w ≠ 0 := by
    intro h0
    have him : (w).im = 0 := by rw [h0]; simp
    have hre : (w).re = 0 := by rw [h0]; simp
    simp [hw] at him hre
    rcases him with h | h
    · have h1 : x 1 = 0 := by simpa [h] using hre
      exact hx0 (by ext i; fin_cases i <;> simp [h, h1])
    · exact absurd h hy.ne'
  have hwpos : 0 < Complex.normSq w := Complex.normSq_pos.mpr hwne
  have hnsq : Complex.normSq w ≤ n ^ 2 * (r + 1) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have := norm_nonneg w
    nlinarith
  set q : ℝ := z.im / (r + 1) ^ 2 with hq
  have hr1 : 0 < (r + 1) ^ 2 := by positivity
  have hq0 : 0 < q := div_pos hy hr1
  have hq1 : q ≤ 1 := by
    rw [div_le_one hr1]
    nlinarith
  have hbase : q / n ^ 2 ≤ z.im / Complex.normSq w := by
    rw [hq, div_div]
    apply div_le_div_of_nonneg_left hy.le hwpos
    nlinarith
  have hqn0 : 0 ≤ q / n ^ 2 := by positivity
  have hstep : (q / n ^ 2) ^ s ≤ (z.im / Complex.normSq w) ^ s :=
    Real.rpow_le_rpow hqn0 hbase (by linarith)
  have hsplit : (q / n ^ 2) ^ s = q ^ s * n ^ (-(2 * s)) := by
    rw [Real.div_rpow hq0.le (by positivity), div_eq_mul_inv, Real.rpow_neg hn0,
      Real.rpow_mul hn0]
    norm_num
  have hq2 : q ^ (2 : ℝ) ≤ q ^ s := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hs2
  have hq2' : 1 / 2 / (r + 1) ^ 4 ≤ q ^ (2 : ℝ) := by
    rw [Real.rpow_two, hq, div_pow, ← pow_mul]
    norm_num
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hnpos : 0 ≤ n ^ (-(2 * s)) := Real.rpow_nonneg hn0 _
  calc 1 / 2 / (r + 1) ^ 4 * n ^ (-(2 * s)) ≤ q ^ s * n ^ (-(2 * s)) :=
        mul_le_mul_of_nonneg_right (hq2'.trans hq2) hnpos
    _ = (q / n ^ 2) ^ s := hsplit.symm
    _ ≤ _ := hstep

end UpperTheory.V.Af.Rs
