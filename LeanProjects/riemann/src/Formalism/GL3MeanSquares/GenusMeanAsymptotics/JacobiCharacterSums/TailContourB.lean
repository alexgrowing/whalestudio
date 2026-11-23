import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailKernel
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronHorizontalSegmentBound

open Complex MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tc_left_pt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z η σ M : ℝ) (hz : 0 < z)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hσ0 : 0 < σ) (hσ1 : σ < 1) (u : ℝ)
    (hM : ‖Formalism.ZeroFreeDirichlet.negLD χ ((σ : ℂ) + (u : ℂ) * I)‖ ≤ M) :
    ‖Formalism.ZeroFreeDirichlet.Fchi χ (z + z * η) ((σ : ℂ) + (u : ℂ) * I) - Formalism.ZeroFreeDirichlet.Fchi χ z ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      M * (4 * η * z ^ σ) * (1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖) := by
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    rw [hre] at h1
    simp at h1
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    simp [hre] at h1
    linarith
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hdiff : ‖((z + z * η : ℝ) : ℂ) ^ s - ((z : ℝ) : ℂ) ^ s‖ ≤
      ‖s‖ * z ^ (σ - 1) * (z + z * η - z) := by
    have hab : z ≤ z + z * η := by nlinarith
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun w : ℝ => ((w : ℂ)) ^ s)
      (f' := fun w : ℝ => s * ((w : ℂ)) ^ (s - 1)) ?_ ?_ (z + z * η) ⟨hab, le_rfl⟩
    · intro w hw
      have hw0 : 0 < w := lt_of_lt_of_le hz hw.1
      have h := (hasStrictDerivAt_cpow_const (c := s) (Complex.ofReal_mem_slitPlane.2 hw0)).hasDerivAt
      exact h.comp_ofReal.hasDerivWithinAt
    · intro w hw
      have hw0 : 0 < w := lt_of_lt_of_le hz hw.1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw0]
      have hre1 : (s - 1).re = σ - 1 := by simp [hre]
      rw [hre1]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hz hw.1 (by linarith))
        (norm_nonneg _)
  have hz1 : z ^ (σ - 1) * (z + z * η - z) = η * z ^ σ := by
    rw [Real.rpow_sub_one hz.ne']
    field_simp
    ring
  have h2 : ‖((z + z * η : ℝ) : ℂ) ^ s - ((z : ℝ) : ℂ) ^ s‖ ≤ ‖s‖ * (η * z ^ σ) := by
    rw [← hz1, ← mul_assoc]
    exact hdiff
  unfold Formalism.ZeroFreeDirichlet.Fchi
  have e : Formalism.ZeroFreeDirichlet.negLD χ s * ((z + z * η : ℝ) : ℂ) ^ s / (s * (s - 1)) -
      Formalism.ZeroFreeDirichlet.negLD χ s * ((z : ℝ) : ℂ) ^ s / (s * (s - 1)) =
      Formalism.ZeroFreeDirichlet.negLD χ s * (((z + z * η : ℝ) : ℂ) ^ s - ((z : ℝ) : ℂ) ^ s) / (s * (s - 1)) := by
    ring
  rw [e, norm_div, norm_mul, norm_mul]
  have hsn : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hs1n : 0 < ‖s - 1‖ := norm_pos_iff.2 hs1
  rw [div_le_iff₀ (by positivity)]
  have key : M * (4 * η * z ^ σ) * (1 / ‖s - 1‖) * (‖s‖ * ‖s - 1‖) =
      4 * (M * (‖s‖ * (η * z ^ σ))) := by
    field_simp
  rw [key]
  have hP : 0 ≤ M * (‖s‖ * (η * z ^ σ)) := by positivity
  have h3 : ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ * ‖((z + z * η : ℝ) : ℂ) ^ s - ((z : ℝ) : ℂ) ^ s‖ ≤
      M * (‖s‖ * (η * z ^ σ)) := mul_le_mul hM h2 (norm_nonneg _) hM0
  linarith

theorem tc_cont {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (y σ u : ℝ) (hy : 0 < y)
    (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hL : DirichletCharacter.LFunction χ ((σ : ℂ) + (u : ℂ) * I) ≠ 0) :
    ContinuousAt (fun v : ℝ => Formalism.ZeroFreeDirichlet.Fchi χ y ((σ : ℂ) + (v : ℂ) * I)) u := by
  have hd : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hline : Continuous (fun v : ℝ => (σ : ℂ) + (v : ℂ) * I) := by fun_prop
  have hs0 : ((σ : ℂ) + (u : ℂ) * I) ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    simp at h1
    linarith
  have hs1 : ((σ : ℂ) + (u : ℂ) * I) - 1 ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    simp at h1
    linarith
  have hG : ContinuousAt (fun s : ℂ => Formalism.ZeroFreeDirichlet.Fchi χ y s) ((σ : ℂ) + (u : ℂ) * I) := by
    unfold Formalism.ZeroFreeDirichlet.Fchi Formalism.ZeroFreeDirichlet.negLD
    have hLc : ContinuousAt (DirichletCharacter.LFunction χ) ((σ : ℂ) + (u : ℂ) * I) :=
      hd.continuous.continuousAt
    have hdL : ContinuousAt (deriv (DirichletCharacter.LFunction χ)) ((σ : ℂ) + (u : ℂ) * I) :=
      (hd.analyticAt _).deriv.continuousAt
    have hcp : ContinuousAt (fun s : ℂ => (y : ℂ) ^ s) ((σ : ℂ) + (u : ℂ) * I) :=
      continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hy.ne')
    apply ContinuousAt.div
    · exact ((hdL.div hLc hL).neg).mul hcp
    · fun_prop
    · exact mul_ne_zero hs0 hs1
  exact ContinuousAt.comp (g := fun s : ℂ => Formalism.ZeroFreeDirichlet.Fchi χ y s) hG hline.continuousAt

theorem tc_right_pt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (C₀ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ 1 / (s.re - 1) + C₀)
    (y t : ℝ) (hy : 0 < y) (ht : t ≠ 0) :
    ‖Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ (1 + C₀) * y ^ 2 / t ^ 2 := by
  set s : ℂ := ((2 : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = 2 := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hN : ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ 1 + C₀ := by
    have h0 := hR s (by rw [hre]; norm_num)
    rw [hre] at h0
    norm_num at h0
    linarith
  have hY : ‖(y : ℂ) ^ s‖ = y ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, hre, Real.rpow_two]
  have h1 : |t| ≤ ‖s‖ := by rw [← him]; exact Complex.abs_im_le_norm s
  have h2 : |t| ≤ ‖s - 1‖ := by
    have e : (s - 1).im = t := by simp [him]
    rw [← e]; exact Complex.abs_im_le_norm _
  have ht2 : 0 < t ^ 2 := by positivity
  have hD : t ^ 2 ≤ ‖s * (s - 1)‖ := by
    rw [norm_mul, ← sq_abs, sq]
    exact mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg _)
  unfold Formalism.ZeroFreeDirichlet.Fchi
  rw [norm_div, norm_mul, hY]
  calc ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ * y ^ 2 / ‖s * (s - 1)‖ ≤ (1 + C₀) * y ^ 2 / ‖s * (s - 1)‖ := by
        gcongr
    _ ≤ (1 + C₀) * y ^ 2 / t ^ 2 := by
        have hC : 0 ≤ 1 + C₀ := le_trans (norm_nonneg _) hN
        exact div_le_div_of_nonneg_left (by positivity) ht2 hD

theorem tc_horiz_pt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (M y T x v : ℝ) (hy : 1 ≤ y)
    (hT : 0 < T) (hv : |v| = T) (hx2 : x ≤ 2)
    (hM : ‖Formalism.ZeroFreeDirichlet.negLD χ ((x : ℂ) + (v : ℂ) * I)‖ ≤ M) :
    ‖Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤ M * y ^ 2 / T ^ 2 := by
  set s : ℂ := (x : ℂ) + (v : ℂ) * I with hs
  have hre : s.re = x := by simp [hs]
  have him : s.im = v := by simp [hs]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hy0 : 0 < y := by linarith
  have hY : ‖(y : ℂ) ^ s‖ ≤ y ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0, hre, ← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hy hx2
  have h1 : T ≤ ‖s‖ := by rw [← hv, ← him]; exact Complex.abs_im_le_norm s
  have h2 : T ≤ ‖s - 1‖ := by
    have e : (s - 1).im = v := by simp [him]
    rw [← hv, ← e]; exact Complex.abs_im_le_norm _
  have hT2 : 0 < T ^ 2 := by positivity
  have hD : T ^ 2 ≤ ‖s * (s - 1)‖ := by
    rw [norm_mul, sq]
    exact mul_le_mul h1 h2 hT.le (norm_nonneg _)
  unfold Formalism.ZeroFreeDirichlet.Fchi
  rw [norm_div, norm_mul]
  calc ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ * ‖(y : ℂ) ^ s‖ / ‖s * (s - 1)‖ ≤ M * y ^ 2 / ‖s * (s - 1)‖ := by
        gcongr
    _ ≤ M * y ^ 2 / T ^ 2 := div_le_div_of_nonneg_left (by positivity) hT2 hD

theorem tc_left_int {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z η σ T M : ℝ)
    (hz : 0 < z) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1 - 1 / 800) (hT : 0 ≤ T)
    (hL : ∀ u : ℝ, |u| ≤ T → DirichletCharacter.LFunction χ ((σ : ℂ) + (u : ℂ) * I) ≠ 0)
    (hM : ∀ u : ℝ, |u| ≤ T → ‖Formalism.ZeroFreeDirichlet.negLD χ ((σ : ℂ) + (u : ℂ) * I)‖ ≤ M) :
    ‖(∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ (z + z * η) ((σ : ℂ) + (u : ℂ) * I))
      - ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ z ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      M * (4 * η * z ^ σ) * (4 * Real.log (1 + 800 * T)) := by
  set δ : ℝ := 1 - σ with hδ
  have hδpos : 0 < δ := by linarith
  have hσpos : 0 < σ := by linarith
  have hσ1' : σ < 1 := by linarith
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by rw [abs_zero]; exact hT))
  have hmem : ∀ u ∈ Set.uIcc (-T) T, |u| ≤ T := by
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    exact abs_le.2 ⟨hu.1, hu.2⟩
  have hc : ∀ w : ℝ, 0 < w → IntervalIntegrable
      (fun u : ℝ => Formalism.ZeroFreeDirichlet.Fchi χ w ((σ : ℂ) + (u : ℂ) * I)) MeasureTheory.volume (-T) T := by
    intro w hw
    apply ContinuousOn.intervalIntegrable
    intro u hu
    exact (tc_cont χ hχ w σ u hw hσpos hσ1' (hL u (hmem u hu))).continuousWithinAt
  have hz1 : 0 < z + z * η := by nlinarith
  rw [← intervalIntegral.integral_sub (hc _ hz1) (hc _ hz)]
  have hK : 0 ≤ M * (4 * η * z ^ σ) := by positivity
  have hpt : ∀ u : ℝ, |u| ≤ T →
      ‖Formalism.ZeroFreeDirichlet.Fchi χ (z + z * η) ((σ : ℂ) + (u : ℂ) * I) - Formalism.ZeroFreeDirichlet.Fchi χ z ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        M * (4 * η * z ^ σ) * (2 / (δ + |u|)) := by
    intro u hu
    refine (tc_left_pt χ z η σ M hz hη hη1 hσpos hσ1' u (hM u hu)).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK
    have hre : ((σ : ℂ) + (u : ℂ) * I - 1).re = σ - 1 := by simp
    have him : ((σ : ℂ) + (u : ℂ) * I - 1).im = u := by simp
    have h1 := Complex.abs_re_le_norm ((σ : ℂ) + (u : ℂ) * I - 1)
    rw [hre, abs_of_neg (by linarith)] at h1
    have h2 := Complex.abs_im_le_norm ((σ : ℂ) + (u : ℂ) * I - 1)
    rw [him] at h2
    have hpos : 0 < δ + |u| := by have := abs_nonneg u; linarith
    rw [div_le_div_iff₀ (by linarith) hpos]
    linarith
  have hgc : Continuous (fun u : ℝ => 2 / (δ + |u|)) :=
    continuous_const.div (by fun_prop)
      (fun u => (by have := abs_nonneg u; linarith : (0 : ℝ) < δ + |u|).ne')
  have hg : IntervalIntegrable (fun u : ℝ => M * (4 * η * z ^ σ) * (2 / (δ + |u|)))
      MeasureTheory.volume (-T) T :=
    (continuous_const.mul hgc).intervalIntegrable _ _
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ hg).trans ?_
  · refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu' : -T < u ∧ u ≤ T := by
      first
        | exact hu
        | (rw [Set.uIoc_of_le (by linarith)] at hu; exact hu)
    exact hpt u (abs_le.2 ⟨hu'.1.le, hu'.2⟩)
  rw [intervalIntegral.integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hK
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hgc.intervalIntegrable _ _)
    (hgc.intervalIntegrable _ _)]
  have hA : ∫ u in (-T)..0, 2 / (δ + |u|) = -2 * Real.log (δ - 0) - -2 * Real.log (δ - -T) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => -2 * Real.log (δ - u))
    · intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      have hpos : 0 < δ - x := by linarith [hx.2]
      have h := (((hasDerivAt_id x).const_sub δ).log hpos.ne').const_mul (-2)
      refine h.congr_deriv ?_
      rw [abs_of_nonpos hx.2]
      try simp only [id_eq]
      ring
    · exact hgc.intervalIntegrable _ _
  have hB : ∫ u in (0 : ℝ)..T, 2 / (δ + |u|) = 2 * Real.log (δ + T) - 2 * Real.log (δ + 0) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => 2 * Real.log (δ + u))
    · intro x hx
      rw [Set.uIcc_of_le hT] at hx
      have hpos : 0 < δ + x := by linarith [hx.1]
      have h := (((hasDerivAt_id x).const_add δ).log hpos.ne').const_mul 2
      refine h.congr_deriv ?_
      rw [abs_of_nonneg hx.1]
      try simp only [id_eq]
      ring
    · exact hgc.intervalIntegrable _ _
  rw [hA, hB]
  simp only [sub_zero, add_zero, sub_neg_eq_add]
  have hq : (δ + T) / δ ≤ 1 + 800 * T := by
    rw [div_le_iff₀ hδpos]
    nlinarith [mul_nonneg hT (by linarith : (0 : ℝ) ≤ 800 * δ - 1)]
  have hlog : Real.log (δ + T) - Real.log δ ≤ Real.log (1 + 800 * T) := by
    rw [← Real.log_div (by linarith) hδpos.ne']
    exact Real.log_le_log (div_pos (by linarith) hδpos) hq
  linarith

theorem tc_norm_comb (E1 E0 a1 b1 a0 b0 V1 V0 : ℂ) :
    ‖(E1 + I * (a1 - b1) + V1) - (E0 + I * (a0 - b0) + V0)‖ ≤
      ‖E1‖ + ‖E0‖ + ‖a1‖ + ‖b1‖ + ‖a0‖ + ‖b0‖ + ‖V1 - V0‖ := by
  have e : (E1 + I * (a1 - b1) + V1) - (E0 + I * (a0 - b0) + V0) =
      E1 - E0 + I * a1 - I * b1 - I * a0 + I * b0 + (V1 - V0) := by ring
  rw [e]
  have h1 := norm_add_le (E1 - E0 + I * a1 - I * b1 - I * a0 + I * b0) (V1 - V0)
  have h2 := norm_add_le (E1 - E0 + I * a1 - I * b1 - I * a0) (I * b0)
  have h3 := norm_sub_le (E1 - E0 + I * a1 - I * b1) (I * a0)
  have h4 := norm_sub_le (E1 - E0 + I * a1) (I * b1)
  have h5 := norm_add_le (E1 - E0) (I * a1)
  have h6 := norm_sub_le E1 E0
  simp only [norm_mul, Complex.norm_I, one_mul] at h2 h3 h4 h5
  linarith

theorem tc_log_bound (Q : ℝ) (hQ : 2 ≤ Q) : Real.log (1 + 800 * (Q / 2)) ≤ 10 * Real.log Q := by
  have hQ0 : 0 < Q := by linarith
  have h1 : 1 + 800 * (Q / 2) ≤ Q ^ 10 := by
    have h9 : (2 : ℝ) ^ 9 * Q ≤ Q ^ 9 * Q :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hQ 9) hQ0.le
    have e : Q ^ 10 = Q ^ 9 * Q := by ring
    rw [e]
    norm_num at h9
    linarith
  calc Real.log (1 + 800 * (Q / 2)) ≤ Real.log (Q ^ 10) := Real.log_le_log (by positivity) h1
    _ = 10 * Real.log Q := by rw [Real.log_pow]; norm_num

end Formalism.HermitianLattices.Ext.BoxTail
