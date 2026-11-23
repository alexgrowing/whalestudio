import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

theorem a_sq_rpow {n : ℝ} (hn : 0 ≤ n) (k : ℕ) : (n ^ 2) ^ ((k : ℝ) / 2) = n ^ k := by
  rw [← Real.rpow_natCast n 2, ← Real.rpow_mul hn, ← Real.rpow_natCast n k]
  congr 1
  push_cast <;> ring

theorem a_rpow_half_sq {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : a ^ ((k : ℝ) / 2) * a ^ ((k : ℝ) / 2) = a ^ k := by
  rw [← Real.mul_rpow ha ha, ← sq, a_sq_rpow ha]

theorem p5 (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : ‖j1 k g z‖ * |(g • z).1.im| ^ ((k : ℝ) / 2) = |z.1.im| ^ ((k : ℝ) / 2) := by
  have hden : den g z.1 ≠ 0 := den_ne g z.2
  have hD : 0 < ‖den g z.1‖ := norm_pos_iff.mpr hden
  have hdet : 0 < |g.val.det| := abs_pos.mpr g.det_ne_zero
  have him : (g • z).1.im = g.val.det * z.1.im / Complex.normSq (den g z.1) := by
    rw [coe_smul, im_div]
  have hns : Complex.normSq (den g z.1) = ‖den g z.1‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have habs : |(g • z).1.im| = |g.val.det| * |z.1.im| / ‖den g z.1‖ ^ 2 := by
    rw [him, hns, abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖den g z.1‖ ^ 2)]
  have hj : ‖j1 k g z‖ = ‖den g z.1‖ ^ k * |g.val.det| ^ (-(k : ℝ) / 2) := by
    rw [j1, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hinv : |g.val.det| ^ (-(k : ℝ) / 2) * |g.val.det| ^ ((k : ℝ) / 2) = 1 := by
    rw [neg_div, Real.rpow_neg (abs_nonneg _), inv_mul_cancel₀ (Real.rpow_pos_of_pos hdet _).ne']
  have hDk : ‖den g z.1‖ ^ k ≠ 0 := pow_ne_zero _ hD.ne'
  rw [hj, habs, Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (abs_nonneg _) (abs_nonneg _),
    a_sq_rpow (norm_nonneg _)]
  rw [show ∀ A B C E : ℝ, A * B * (C * E / A) = (B * C) * E * (A / A) from fun _ _ _ _ => by ring,
    hinv, div_self hDk, one_mul, mul_one]

theorem a_sub_conj_ne (z w : P) (h : 0 < z.1.im * w.1.im) : z.1 - conj w.1 ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
  have hzw : z.1.im = -w.1.im := by linarith
  rw [hzw] at h
  nlinarith [sq_nonneg w.1.im]

theorem p6 (k : ℕ) (z w : P) (hk : 1 ≤ k) : ‖q1 k z w‖ * |z.1.im| ^ ((k : ℝ) / 2) = ((k : ℝ) - 1) / (4 * Real.pi) * kap z w ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) / 2 ≠ 0 := by
    intro h0
    linarith
  by_cases h : 0 < z.1.im * w.1.im
  · have hq : q1 k z w = ((k : ℂ) - 1) / (4 * Real.pi) * ((w.1 - conj w.1) / (z.1 - conj w.1)) ^ k := by
      rw [q1, if_pos h]
    have hkap : kap z w = 4 * (z.1.im * w.1.im) / ‖z.1 - conj w.1‖ ^ 2 := by
      rw [kap, if_pos h]
    have hd : z.1 - conj w.1 ≠ 0 := a_sub_conj_ne z w h
    have hdn : 0 < ‖z.1 - conj w.1‖ := norm_pos_iff.mpr hd
    have hww : ‖w.1 - conj w.1‖ = 2 * |w.1.im| := by
      rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    have hc : ‖((k : ℂ) - 1) / (4 * Real.pi)‖ = ((k : ℝ) - 1) / (4 * Real.pi) := by
      have hpi := Real.pi_pos
      have e : ((k : ℂ) - 1) / (4 * Real.pi) = ((((k : ℝ) - 1) / (4 * Real.pi) : ℝ) : ℂ) := by
        push_cast <;> ring
      rw [e, Complex.norm_real, Real.norm_of_nonneg (by apply div_nonneg <;> linarith)]
    have hzw : z.1.im * w.1.im = |z.1.im| * |w.1.im| := by
      rw [← abs_mul, abs_of_pos h]
    have h4 : (4 : ℝ) ^ ((k : ℝ) / 2) = 2 ^ k := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, a_sq_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hq, norm_mul, hc, norm_pow, norm_div, hww, hkap, hzw,
      Real.div_rpow (by positivity) (by positivity), a_sq_rpow hdn.le,
      Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (abs_nonneg _) (abs_nonneg _), h4,
      div_pow, mul_pow, ← a_rpow_half_sq (abs_nonneg w.1.im) k]
    ring
  · have hq : q1 k z w = 0 := by
      rw [q1, if_neg h]
    have hkap : kap z w = 0 := by
      rw [kap, if_neg h]
    rw [hq, hkap, norm_zero, zero_mul, Real.zero_rpow hk0, mul_zero, zero_mul]

end UpperTheory.Esk.AutomorphyFactorLemmas
