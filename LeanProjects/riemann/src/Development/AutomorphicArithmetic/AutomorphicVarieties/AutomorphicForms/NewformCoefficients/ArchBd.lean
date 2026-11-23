import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt

open UpperHalfPlane hiding I
open CongruenceSubgroup

theorem UpperTheory.V.Af.Nf.archBd :
    UpperTheory.V.Af.Nf.ArchBd := by
  intro k M hM f
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨C, fun x hx => ?_⟩
  unfold UpperTheory.V.Af.Nf.nsl
  set J : ℂ := (x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ) with hJdef
  set w : ℂ := (((SignType.sign x.det : ℝ)) : ℂ) *
    (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) / J) with hwdef
  have hJ0 : J ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [J] at h1 h2
    apply hx
    rw [Matrix.det_fin_two, h1, h2]
    ring
  have hn : Complex.normSq J = ‖J‖ ^ 2 := Complex.normSq_eq_norm_sq J
  have hJpos : 0 < ‖J‖ := norm_pos_iff.mpr hJ0
  have hDpos : 0 < |x.det| := abs_pos.mpr hx
  have hq : (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) / J).im =
      x.det / Complex.normSq J := by
    rw [Complex.div_im, Matrix.det_fin_two]
    simp [J]
    ring
  have himw : w.im = |x.det| / ‖J‖ ^ 2 := by
    rw [hwdef, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hq, hn]
    rcases lt_or_gt_of_ne hx with h | h
    · rw [sign_neg h, abs_of_neg h]
      simp
      ring
    · rw [sign_pos h, abs_of_pos h]
      simp
  have hw : 0 < w.im := by
    rw [himw]
    positivity
  have hτ : (ofComplex w).im = |x.det| / ‖J‖ ^ 2 := by
    rw [← himw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    all_goals rfl
  have hb := hC (ofComplex w)
  rw [hτ] at hb
  have hpow : (|x.det| / ‖J‖ ^ 2) ^ (((k : ℤ) : ℝ) / 2) = |x.det| ^ ((k : ℝ) / 2) / ‖J‖ ^ k := by
    rw [Real.div_rpow hDpos.le (by positivity), ← Real.rpow_natCast ‖J‖ 2,
      ← Real.rpow_mul hJpos.le]
    push_cast
    congr 1
    rw [show (2 : ℝ) * ((k : ℝ) / 2) = ((k : ℕ) : ℝ) by ring, Real.rpow_natCast]
  rw [hpow] at hb
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_zpow]
  calc _ ≤ |x.det| ^ ((k : ℝ) / 2) * ‖J‖ ^ (-(k : ℤ)) *
        (C / (|x.det| ^ ((k : ℝ) / 2) / ‖J‖ ^ k)) := by gcongr
    _ = C := by
      have h1 : 0 < |x.det| ^ ((k : ℝ) / 2) := by positivity
      have h2 : 0 < ‖J‖ ^ k := by positivity
      rw [zpow_neg, zpow_natCast]
      field_simp
