import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory in
theorem UpperTheory.V.Af.Rs.tBdd :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.ZDiff → UpperTheory.V.Af.Rs.ZInt → UpperTheory.V.Af.Rs.TBdd := by
  intro hF hD _ L _ G hG h0
  obtain ⟨C, hC⟩ := hD L
  obtain ⟨-, D, hD⟩ := hG
  refine ⟨(∑ _v : Fin 2 → ZMod L, |C| * D) * (volume : Measure UpperHalfPlane).real ModularGroup.fd, fun s hs => ?_⟩
  unfold UpperTheory.V.Af.Rs.TT
  refine norm_setIntegral_le_of_norm_le_const hF.2 fun z hz => ?_
  have hy : 0 < z.im := z.im_pos
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hy2 : 1 / 2 ≤ z.im := by nlinarith
  have he : ∑ v, G v z * (UpperTheory.V.Af.Rs.Zc L v s z : ℂ) =
      ∑ v, G v z * ((UpperTheory.V.Af.Rs.Zc L v s z - UpperTheory.V.Af.Rs.Zc L 0 s z : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h0 z, zero_mul, sub_zero]
  rw [he]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := hC v 0 s hs z hz
  have h2 := hD v z hy2
  have h4 : C * z.im ^ 3 ≤ |C| * z.im ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  calc _ ≤ ‖G v z‖ * (|C| * z.im ^ 3) := mul_le_mul_of_nonneg_left (h1.trans h4) (norm_nonneg _)
    _ = |C| * (‖G v z‖ * z.im ^ 3) := by ring
    _ ≤ |C| * D := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
