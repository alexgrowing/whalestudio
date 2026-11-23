import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped ENNReal

private lemma fd_meas : MeasurableSet ModularGroup.fd := by
  apply IsClosed.measurableSet
  have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
    isClosed_le (UpperHalfPlane.continuous_re.abs) continuous_const
  exact h1.inter h2

private lemma tail_fin :
    ∫⁻ y in Ioi (1 / 2 : ℝ), ENNReal.ofReal (1 / y ^ 2) < ∞ := by
  have h : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi (1 / 2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h' : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Ioi (1 / 2 : ℝ)) := by
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) ≤ y := le_trans (by norm_num) (le_of_lt hy)
    simp only
    rw [Real.rpow_neg hy0, Real.rpow_two, one_div]
  exact h'.lintegral_lt_top

theorem UpperTheory.V.Af.Rs.fdFin :
    UpperTheory.V.Af.Rs.StripIm → UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdFin := by
  rintro - ⟨hm, hv⟩
  refine ⟨fd_meas, ?_⟩
  rw [hv, Measure.map_apply hm fd_meas]
  have hsub : (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' ModularGroup.fd ⊆
      (Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Ioi (1 / 2 : ℝ)) ∪ ((univ : Set ℝ) ×ˢ Iic (0 : ℝ)) := by
    rintro ⟨x, y⟩ hp
    rcases le_or_gt y 0 with hy | hy
    · exact Or.inr ⟨mem_univ _, hy⟩
    · left
      have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
      have hp' : UpperTheory.V.Af.Rs.pt x y ∈ ModularGroup.fd := hp
      have e : UpperTheory.V.Af.Rs.pt x y = ⟨_, him⟩ := ofComplex_apply_of_im_pos him
      have hre : (UpperTheory.V.Af.Rs.pt x y).re = x := by rw [e]; simp [UpperHalfPlane.re]
      have hi : (UpperTheory.V.Af.Rs.pt x y).im = y := by rw [e]; simp [UpperHalfPlane.im]
      have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hp'
      have h2 := hp'.2
      rw [hre] at h2
      rw [hi] at h3
      refine ⟨abs_le.1 h2, ?_⟩
      show (1 / 2 : ℝ) < y
      nlinarith
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
  rw [ENNReal.add_lt_top]
  constructor
  · rw [withDensity_apply _ (measurableSet_Icc.prod measurableSet_Ioi), ← Measure.prod_restrict,
      lintegral_prod _ (by fun_prop)]
    simp only [lintegral_const]
    rw [Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.2 (Ioi_subset_Ioi (by norm_num))]
    exact ENNReal.mul_lt_top tail_fin (by simp)
  · rw [withDensity_absolutelyContinuous _ _ (by simp [Measure.prod_prod, Iic_inter_Ioi])]
    exact ENNReal.zero_lt_top
