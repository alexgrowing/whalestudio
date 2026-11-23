import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PerZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.DownHol
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CuspMean

noncomputable section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
open UpperHalfPlane hiding I

namespace UpperTheory.V.Br

private theorem aff_mul' (y z : ℝˣ) (x t : ℝ) : aff y x * aff z t = aff (y * z) (x + y * t) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem aff_one' : aff (1 : ℝˣ) (0 : ℝ) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_inv' (y : ℝˣ) (x : ℝ) : (aff y x)⁻¹ = aff y⁻¹ (-((y⁻¹ : ℝˣ) * x)) := by
  refine inv_eq_of_mul_eq_one_left ?_
  rw [aff_mul', inv_mul_cancel, neg_add_cancel, aff_one']

private theorem down_vadd (k : ℕ) (φ : GA ℚ 2 → ℂ) (t : ℝ) (z : ℍ) :
    down k φ (t +ᵥ z) = ((z.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) *
      φ (upR (aff 1 t) * (1 * upR (aff (Units.mk0 z.im z.im_pos.ne') z.re))) := by
  rw [one_mul, ← map_mul, aff_mul', one_mul]
  unfold down
  have h : Units.mk0 (t +ᵥ z).im (t +ᵥ z).im_pos.ne' = Units.mk0 z.im z.im_pos.ne' := Units.ext (vadd_im t z)
  rw [h, vadd_im, vadd_re]
  simp

private theorem norm_aff (y : ℝˣ) (x B : ℝ) (h1 : 1 ≤ B) (hy : |(y : ℝ)| ≤ B) (hx : |x| ≤ B) :
    ‖TR.toL (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (aff y x)).val‖ ≤ B := by
  have h0 : 0 ≤ B := zero_le_one.trans h1
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
    (pi_norm_le_iff_of_nonneg h0).2 fun v => ?_
  change |(aff y x).val i j| ≤ B
  fin_cases i <;> fin_cases j <;> simp [aff, *]

private theorem height_aff (N : ℕ) (hN : 0 < N) (z : ℍ) (h1 : 1 ≤ z.im) (h2 : |z.re| ≤ N) :
    TR.height (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (aff (Units.mk0 z.im z.im_pos.ne') z.re)) ≤
      3 * N * z.im := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB : (1 : ℝ) ≤ N * z.im := by nlinarith
  have hB2 : (N : ℝ) ≤ N * z.im := by nlinarith
  have hi : |(z.im)⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.2 z.im_pos)]; exact inv_le_one_of_one_le₀ h1
  have a1 := norm_aff (Units.mk0 z.im z.im_pos.ne') z.re (N * z.im) hB
    (by rw [Units.val_mk0, abs_of_pos z.im_pos]; nlinarith) (h2.trans hB2)
  have a2 := norm_aff (Units.mk0 z.im z.im_pos.ne')⁻¹ (-(((Units.mk0 z.im z.im_pos.ne')⁻¹ : ℝˣ) * z.re)) (N * z.im) hB
    (by rw [Units.val_inv_eq_inv_val, Units.val_mk0]; exact hi.trans hB)
    (by
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, abs_neg, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hi).trans (h2.trans hB2))
  unfold TR.height
  rw [← map_inv, aff_inv']
  linarith

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.downZero :
    UpperTheory.V.Br.DownZero := by
  intro k φ hc hl
  obtain ⟨N, hN, hm⟩ := cuspMean φ hc 1
  obtain ⟨C, m, hg⟩ := hc.1.growth 1
  refine perZero _ N hN (downHol k φ hl) (fun z => ?_) ⟨|C| * (3 * N) ^ m, m, fun z h1 h2 => ?_⟩ fun z => ?_
  · have h := (hm (aff (Units.mk0 z.im z.im_pos.ne') z.re)).1 0
    have h0 := down_vadd k φ.1 0 z
    rw [zero_vadd] at h0
    rw [down_vadd, h0]
    simp only [zero_add] at h
    rw [h]
  · have h := hg (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (aff (Units.mk0 z.im z.im_pos.ne') z.re))
    rw [one_mul] at h
    have h3 := height_aff N hN z h1 h2
    have h4 : 0 ≤ TR.height (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ))
        (aff (Units.mk0 z.im z.im_pos.ne') z.re)) := by
      unfold TR.height; positivity
    have h5 : z.im ^ (-((k : ℝ) / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (neg_nonpos.2 (by positivity))
    unfold down
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg z.im_pos.le _)]
    refine (mul_le_of_le_one_left (norm_nonneg _) h5).trans (h.trans ?_)
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ h4 h3 m) (pow_nonneg h4 m) (abs_nonneg C)
  · simp only [down_vadd]
    rw [intervalIntegral.integral_const_mul, (hm _).2, mul_zero]
