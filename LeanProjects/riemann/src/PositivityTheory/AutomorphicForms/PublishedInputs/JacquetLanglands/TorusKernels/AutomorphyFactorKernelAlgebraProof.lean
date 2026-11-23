import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ARpowHalfSq
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.BNeg

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

theorem den_mul (g h : GL (Fin 2) ℝ) (z : P) : den (g * h) z.1 = den g (h • z).1 * den h z.1 := by
  have h0 := den_ne h z.2
  rw [coe_smul]
  conv_rhs => rw [den, add_mul, mul_assoc, div_mul_cancel₀ _ h0]
  simp [num, den, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem p1 (k : ℕ) (g h : GL (Fin 2) ℝ) (z : P) : j1 k (g * h) z = j1 k g (h • z) * j1 k h z := by
  simp only [j1, den_mul, mul_pow, Units.val_mul, Matrix.det_mul, abs_mul,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _), Complex.ofReal_mul]
  ring

theorem p2 (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : j1 k g z ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (den_ne g z.2))
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (abs_pos.2 g.det_ne_zero) _).ne')

theorem im_smul (g : GL (Fin 2) ℝ) (z : P) :
    (g • z).1.im = g.val.det * z.1.im / Complex.normSq (den g z.1) := by
  rw [coe_smul, im_div]

theorem sub_conj (g : GL (Fin 2) ℝ) (z w : P) :
    (g • z).1 - conj (g • w).1 = (g.val.det : ℂ) * (z.1 - conj w.1) / (den g z.1 * conj (den g w.1)) := by
  rw [coe_smul, coe_smul, map_div₀, div_sub_div _ _ (den_ne g z.2) ((map_ne_zero _).2 (den_ne g w.2))]
  congr 1
  simp only [num, den, map_add, map_mul, Complex.conj_ofReal, det_eq]
  push_cast
  ring

theorem sign (g : GL (Fin 2) ℝ) (z w : P) : 0 < (g • z).1.im * (g • w).1.im ↔ 0 < z.1.im * w.1.im := by
  rw [im_smul, im_smul]
  have hd : g.val.det ≠ 0 := g.det_ne_zero
  have nz : 0 < Complex.normSq (den g z.1) := Complex.normSq_pos.2 (den_ne g z.2)
  have nw : 0 < Complex.normSq (den g w.1) := Complex.normSq_pos.2 (den_ne g w.2)
  have hc : 0 < g.val.det ^ 2 / (Complex.normSq (den g z.1) * Complex.normSq (den g w.1)) :=
    div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hd))) (mul_pos nz nw)
  rw [show g.val.det * z.1.im / Complex.normSq (den g z.1) * (g.val.det * w.1.im / Complex.normSq (den g w.1))
      = g.val.det ^ 2 / (Complex.normSq (den g z.1) * Complex.normSq (den g w.1)) * (z.1.im * w.1.im) by
    field_simp]
  exact ⟨fun h => pos_of_mul_pos_right h hc.le, fun h => mul_pos hc h⟩

theorem ratio (g : GL (Fin 2) ℝ) (z w : P) (h : 0 < z.1.im * w.1.im) :
    ((g • w).1 - conj (g • w).1) / ((g • z).1 - conj (g • w).1)
      = (w.1 - conj w.1) / (z.1 - conj w.1) * (den g z.1 / den g w.1) := by
  have hd : (g.val.det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 g.det_ne_zero
  have h1 := den_ne g z.2
  have h2 := den_ne g w.2
  have h3 : conj (den g w.1) ≠ 0 := (map_ne_zero _).2 h2
  have h4 : z.1 - conj w.1 ≠ 0 := b_ne _ _ h
  have h5 : w.1 - conj w.1 ≠ 0 := b_ne _ _ (mul_self_pos.2 w.2)
  rw [sub_conj, sub_conj]
  field_simp

theorem p3 (k : ℕ) (g : GL (Fin 2) ℝ) (z w : P) :
    q1 k (g • z) (g • w) * j1 k g w = j1 k g z * q1 k z w := by
  unfold q1
  rw [if_congr (sign g z w) rfl rfl]
  split_ifs with h
  · rw [ratio g z w h, mul_pow, div_pow (den g z.1)]
    have h2 := pow_ne_zero k (den_ne g w.2)
    simp only [j1]
    field_simp
  · simp

theorem p4 (g : GL (Fin 2) ℝ) (z w : P) : kap (g • z) (g • w) = kap z w := by
  unfold kap
  rw [if_congr (sign g z w) rfl rfl]
  split_ifs with h
  · have hd : g.val.det ≠ 0 := g.det_ne_zero
    have nz : 0 < Complex.normSq (den g z.1) := Complex.normSq_pos.2 (den_ne g z.2)
    have nw : 0 < Complex.normSq (den g w.1) := Complex.normSq_pos.2 (den_ne g w.2)
    have h4 : ‖z.1 - conj w.1‖ ≠ 0 := norm_ne_zero_iff.2 (b_ne _ _ h)
    rw [im_smul, im_smul, sub_conj, norm_div, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, div_pow, mul_pow, mul_pow, sq_abs]
    simp only [Complex.sq_norm]
    field_simp
  · rfl

end UpperTheory.Esk.AutomorphyFactorLemmas

namespace UpperTheory.Esk

open AutomorphyFactorLemmas in
theorem automorphy_factor_kernel_algebra_proof : B1b :=
  ⟨p1, p2, p3, p4, p5, fun k z w hk => p6 k z w hk, p7, p8, p9⟩

end UpperTheory.Esk
