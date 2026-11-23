import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt

open UpperHalfPlane

namespace UpperTheory.V.Af.Nf

end UpperTheory.V.Af.Nf

private theorem lower_row_mul_add_ne_zero_of_det_ne_zero (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) (w : ℍ) :
    (x 1 0 : ℂ) * (w : ℂ) + (x 1 1 : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rcases him with h1 | h1
  · apply hx
    rw [Matrix.det_fin_two]
    simp [h1] at hre
    simp [h1, hre]
  · exact absurd h1 w.im_pos.ne'

private theorem im_mobius_pos_of_det_pos (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : 0 < y.det) (z : ℍ) :
    0 < (((y 0 0 : ℂ) * z + y 0 1) / ((y 1 0 : ℂ) * z + y 1 1)).im := by
  have hj := lower_row_mul_add_ne_zero_of_det_ne_zero y hy.ne' z
  rw [Complex.div_im]
  have hn : 0 < Complex.normSq ((y 1 0 : ℂ) * z + y 1 1) := Complex.normSq_pos.mpr hj
  rw [← sub_div]
  apply div_pos _ hn
  have hd := hy
  rw [Matrix.det_fin_two] at hd
  simp
  nlinarith [z.im_pos]

open UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.nslMul :
    UpperTheory.V.Af.Nf.NslMul := by
  intro k f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    funext z
    have hjy := lower_row_mul_add_ne_zero_of_det_ne_zero y hy.ne' z
    have hm := im_mobius_pos_of_det_pos y hy z
    set m := ((y 0 0 : ℂ) * z + y 0 1) / ((y 1 0 : ℂ) * z + y 1 1) with hmdef
    simp only [nsl]
    rw [sign_pos hy, Matrix.det_mul, sign_mul, sign_pos hy, mul_one, abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    simp only [SignType.coe_one, Int.cast_one, Complex.ofReal_one, one_mul]
    rw [← hmdef, UpperHalfPlane.ofComplex_apply_of_im_pos hm]
    simp only [UpperHalfPlane.coe_mk, Matrix.mul_apply, Fin.sum_univ_two]
    have hJ : ((↑(x 1 0 * y 0 0 + x 1 1 * y 1 0) : ℂ) * z + ↑(x 1 0 * y 0 1 + x 1 1 * y 1 1)) =
        ((x 1 0 : ℂ) * m + x 1 1) * ((y 1 0 : ℂ) * z + y 1 1) := by
      rw [hmdef, add_mul, mul_assoc, div_mul_cancel₀ _ hjy]
      push_cast
      ring
    have hN : ((↑(x 0 0 * y 0 0 + x 0 1 * y 1 0) : ℂ) * z + ↑(x 0 0 * y 0 1 + x 0 1 * y 1 1)) =
        ((x 0 0 : ℂ) * m + x 0 1) * ((y 1 0 : ℂ) * z + y 1 1) := by
      rw [hmdef, add_mul, mul_assoc, div_mul_cancel₀ _ hjy]
      push_cast
      ring
    rw [hJ, hN, mul_div_mul_right _ _ hjy, mul_zpow]
    push_cast
    ring
  · intro x
    funext z
    simp only [nsl, eps, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp
    have h1 : -(x 0 0 * x 1 1) + x 0 1 * x 1 0 = -(x 0 0 * x 1 1 - x 0 1 * x 1 0) := by ring
    rw [h1, abs_neg, Left.sign_neg]
    congr 3
    push_cast
    ring
  · intro t x ht
    funext z
    simp only [nsl, Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]
    have h1 : t * x 0 0 * (t * x 1 1) - t * x 0 1 * (t * x 1 0) =
        t ^ 2 * (x 0 0 * x 1 1 - x 0 1 * x 1 0) := by ring
    rw [h1]
    set d := x 0 0 * x 1 1 - x 0 1 * x 1 0
    have h2 : SignType.sign (t ^ 2 * d) = SignType.sign d := by
      rw [sign_mul, sign_pos (by positivity), one_mul]
    have h3 : |t ^ 2 * d| ^ ((k : ℝ) / 2) = t ^ k * |d| ^ ((k : ℝ) / 2) := by
      rw [abs_mul, Real.mul_rpow (by positivity) (abs_nonneg _),
        abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]
      congr 1
      rw [show (t ^ 2 : ℝ) = t ^ (2:ℝ) by norm_cast, ← Real.rpow_mul ht.le,
        show (2:ℝ) * (k / 2) = k by ring, Real.rpow_natCast]
    have hj : ((↑(t * x 1 0) : ℂ) * ↑z + ↑(t * x 1 1)) = (t : ℂ) * ((x 1 0 : ℂ) * z + x 1 1) := by
      push_cast
      ring
    have hn : ((↑(t * x 0 0) : ℂ) * ↑z + ↑(t * x 0 1)) = (t : ℂ) * ((x 0 0 : ℂ) * z + x 0 1) := by
      push_cast
      ring
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [h2, h3, hj, hn, mul_div_mul_left _ _ ht']
    congr 1
    push_cast
    rw [mul_zpow, zpow_neg, zpow_neg, zpow_natCast]
    field_simp
  · intro c x
    funext z
    simp only [nsl, Pi.smul_apply, smul_eq_mul]
    ring
