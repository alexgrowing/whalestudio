import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern

open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B

noncomputable section

namespace GlobalTheory.CompanionTheory.MajC

theorem kern_nonneg' (s T : ℝ) (hT : 0 < T) (z : ℂ) : 0 ≤ kern s T z := by
  unfold kern
  refine mul_nonneg (by positivity) (le_min ?_ ?_)
  · exact Real.rpow_nonneg (by positivity) _
  · exact Real.rpow_nonneg (by positivity) _

theorem gm_nonneg' (ε β : ℝ) (m : ℕ) (hβ : 0 < β) (h : M22) : 0 ≤ gm ε β m h := by
  unfold gm
  split_ifs with hc
  · have h1 : 0 ≤ β ^ (-ε) := Real.rpow_nonneg hβ.le _
    have h2 : 0 ≤ ‖h 0 0‖ ^ (-4 + ε) := Real.rpow_nonneg (norm_nonneg _) _
    have h3 := kern_nonneg' ε β hβ (h 1 1 - h 1 0 / h 0 0 * h 0 1)
    positivity
  · exact le_rfl

theorem radial_bound (ε β r : ℝ) (N : ℕ) (hε : 0 < ε) (hβ : 0 < β) (hr : 0 < r)
    (hN : 2 * ε ≤ N) :
    r ^ (-(2 + ε)) * ((1 + β / r) ^ N)⁻¹ ≤
      β ^ (-ε) * ((r ^ 2)⁻¹ * min ((r / β) ^ ε) ((β / r) ^ ε)) := by
  have hw : 0 < β / r := div_pos hβ hr
  set a := r ^ ε with ha
  set b := β ^ ε with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hr _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hβ _
  set W := (1 + β / r) ^ N with hWdef
  have hW1 : 1 ≤ W := one_le_pow₀ (by linarith)
  have hW0 : 0 < W := by linarith
  have e1 : (β / r) ^ ε = b / a := Real.div_rpow hβ.le hr.le _
  have e2 : (r / β) ^ ε = a / b := Real.div_rpow hr.le hβ.le _
  have e3 : r ^ (-(2 + ε)) = (r ^ 2)⁻¹ * a⁻¹ := by
    rw [neg_add, Real.rpow_add hr, Real.rpow_neg hr.le, Real.rpow_neg hr.le, Real.rpow_two]
  have e4 : β ^ (-ε) = b⁻¹ := Real.rpow_neg hβ.le _
  have hW2 : (b / a) ^ 2 ≤ W := by
    have s1 : (b / a) ^ 2 = (β / r) ^ (2 * ε) := by
      rw [← e1, mul_comm, Real.rpow_mul hw.le, Real.rpow_two]
    have s2 : (β / r) ^ (2 * ε) ≤ (1 + β / r) ^ (2 * ε) :=
      Real.rpow_le_rpow hw.le (by linarith) (by positivity)
    have s3 : (1 + β / r) ^ (2 * ε) ≤ (1 + β / r) ^ (N : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hN
    rw [Real.rpow_natCast] at s3
    rw [s1]
    exact s2.trans s3
  rw [e1, e2, e3, e4]
  have hr2 : 0 < (r ^ 2)⁻¹ := by positivity
  have key : a⁻¹ * W⁻¹ ≤ b⁻¹ * min (a / b) (b / a) := by
    rw [mul_min_of_nonneg _ _ (by positivity)]
    refine le_min ?_ ?_
    · have : W⁻¹ ≤ ((b / a) ^ 2)⁻¹ := inv_anti₀ (by positivity) hW2
      calc a⁻¹ * W⁻¹ ≤ a⁻¹ * ((b / a) ^ 2)⁻¹ := by gcongr
        _ = b⁻¹ * (a / b) := by field_simp
    · have : W⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
      calc a⁻¹ * W⁻¹ ≤ a⁻¹ * 1 := by gcongr
        _ = b⁻¹ * (b / a) := by field_simp
  calc (r ^ 2)⁻¹ * a⁻¹ * W⁻¹ = (r ^ 2)⁻¹ * (a⁻¹ * W⁻¹) := by ring
    _ ≤ (r ^ 2)⁻¹ * (b⁻¹ * min (a / b) (b / a)) := by gcongr
    _ = b⁻¹ * ((r ^ 2)⁻¹ * min (a / b) (b / a)) := by ring

theorem dt_eq (h : M22) : dt h = ‖h 0 0 * h 1 1 - h 0 1 * h 1 0‖ := by
  unfold dt
  rw [Matrix.det_fin_two]
  simp [Matrix.of_apply]

theorem dt_swp (h : M22) : dt (swp h) = dt h := by
  rw [dt_eq, dt_eq]
  have : (swp h) 0 0 * (swp h) 1 1 - (swp h) 0 1 * (swp h) 1 0
      = -(h 0 0 * h 1 1 - h 0 1 * h 1 0) := by
    simp [swp]; ring
  rw [this, norm_neg]

theorem col_swp (h : M22) : col (swp h) = col h := by
  simp [col, swp, max_comm]

theorem norm_swp_le (h : M22) : ‖swp h‖ ≤ ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  fin_cases i
  · simpa [swp] using norm_le_pi_norm h 1
  · simpa [swp] using norm_le_pi_norm h 0

theorem swp_swp (h : M22) : swp (swp h) = h := by
  funext i
  fin_cases i <;> simp [swp]

theorem norm_swp (h : M22) : ‖swp h‖ = ‖h‖ :=
  le_antisymm (norm_swp_le h) (by simpa [swp_swp] using norm_swp_le (swp h))

theorem hm_swp (ε β : ℝ) (N : ℕ) (h : M22) : hm ε N β (swp h) = hm ε N β h := by
  unfold hm
  rw [dt_swp, col_swp, norm_swp]

theorem entry_le (h : M22) (i j : Fin 2) : ‖h i j‖ ≤ ‖h‖ :=
  (norm_le_pi_norm (h i) j).trans (norm_le_pi_norm h i)

theorem one_region (ε β : ℝ) (m N : ℕ) (hε : 0 < ε) (hβ : 0 < β) (hm' : 2 * ε ≤ m)
    (hN : 2 * m ≤ N) (h : M22) (hv : ‖h 1 0‖ ≤ ‖h 0 0‖) (hd : dt h ≠ 0) :
    hm ε N β h ≤ gm ε β m h := by
  have hu : h 0 0 ≠ 0 := by
    intro hu
    have hv0 : h 1 0 = 0 := by
      rw [hu, norm_zero] at hv
      exact norm_le_zero_iff.1 hv
    apply hd
    rw [dt_eq, hu, hv0]
    simp
  set z := h 1 1 - h 1 0 / h 0 0 * h 0 1 with hz
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = h 0 0 * z := by
    rw [hz]; field_simp
  have hU : 0 < ‖h 0 0‖ := norm_pos_iff.2 hu
  have hdt : dt h = ‖h 0 0‖ * ‖z‖ := by rw [dt_eq, hdet, norm_mul]
  have hr : 0 < ‖z‖ := by
    have : 0 < dt h := lt_of_le_of_ne (by rw [dt_eq]; exact norm_nonneg _) (Ne.symm hd)
    rw [hdt] at this
    exact (pos_iff_pos_of_mul_pos this).1 hU
  have hcol : col h = ‖h 0 0‖ := max_eq_left hv
  have hgm : gm ε β m h = β ^ (-ε) * ‖h 0 0‖ ^ (-4 + ε) * ((1 + ‖h 0 0‖) ^ m)⁻¹ *
      ((1 + ‖h 0 1‖) ^ m)⁻¹ * kern ε β z := by
    unfold gm
    rw [if_pos ⟨hv, hu⟩]
  rw [hgm]
  have hfrac : β * (‖h 0 0‖ / (‖h 0 0‖ * ‖z‖)) = β / ‖z‖ := by field_simp
  have hpow : (‖h 0 0‖ * ‖z‖) ^ (-(2 + ε)) * ‖h 0 0‖ ^ (-2 + 2 * ε)
      = ‖h 0 0‖ ^ (-4 + ε) * ‖z‖ ^ (-(2 + ε)) := by
    rw [Real.mul_rpow hU.le hr.le, mul_right_comm, ← Real.rpow_add hU]
    congr 2
    ring
  have hA : ((1 + ‖h‖) ^ N)⁻¹ ≤ ((1 + ‖h 0 0‖) ^ m)⁻¹ * ((1 + ‖h 0 1‖) ^ m)⁻¹ := by
    rw [← mul_inv]
    apply inv_anti₀ (by positivity)
    have h1 : 1 + ‖h 0 0‖ ≤ 1 + ‖h‖ := by linarith [entry_le h 0 0]
    have h2 : 1 + ‖h 0 1‖ ≤ 1 + ‖h‖ := by linarith [entry_le h 0 1]
    have h3 : (1 : ℝ) ≤ 1 + ‖h‖ := by linarith [norm_nonneg h]
    calc (1 + ‖h 0 0‖) ^ m * (1 + ‖h 0 1‖) ^ m
        ≤ (1 + ‖h‖) ^ m * (1 + ‖h‖) ^ m := by gcongr
      _ = (1 + ‖h‖) ^ (2 * m) := by rw [two_mul, pow_add]
      _ ≤ (1 + ‖h‖) ^ N := pow_le_pow_right₀ h3 hN
  have hN' : 2 * ε ≤ (N : ℝ) := by
    have : (m : ℝ) ≤ N := by
      have : m ≤ N := by omega
      exact_mod_cast this
    linarith
  have hB := radial_bound ε β ‖z‖ N hε hβ hr hN'
  have hk : kern ε β z = (‖z‖ ^ 2)⁻¹ * min ((‖z‖ / β) ^ ε) ((β / ‖z‖) ^ ε) := rfl
  unfold hm
  rw [hdt, hcol, hfrac, hpow, hk]
  have hUp : 0 ≤ ‖h 0 0‖ ^ (-4 + ε) := Real.rpow_nonneg hU.le _
  have hzp : 0 ≤ ‖z‖ ^ (-(2 + ε)) * ((1 + β / ‖z‖) ^ N)⁻¹ := by
    have := Real.rpow_nonneg hr.le (-(2 + ε))
    positivity
  calc ‖h 0 0‖ ^ (-4 + ε) * ‖z‖ ^ (-(2 + ε)) * ((1 + ‖h‖) ^ N)⁻¹ * ((1 + β / ‖z‖) ^ N)⁻¹
      = ‖h 0 0‖ ^ (-4 + ε) * (((1 + ‖h‖) ^ N)⁻¹ *
          (‖z‖ ^ (-(2 + ε)) * ((1 + β / ‖z‖) ^ N)⁻¹)) := by ring
    _ ≤ ‖h 0 0‖ ^ (-4 + ε) * ((((1 + ‖h 0 0‖) ^ m)⁻¹ * ((1 + ‖h 0 1‖) ^ m)⁻¹) *
          (β ^ (-ε) * ((‖z‖ ^ 2)⁻¹ * min ((‖z‖ / β) ^ ε) ((β / ‖z‖) ^ ε)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hUp
        exact mul_le_mul hA hB hzp (by positivity)
    _ = _ := by ring

theorem hm_le_gm_add (ε β : ℝ) (m N : ℕ) (hε : 0 < ε) (hβ : 0 < β) (hm' : 2 * ε ≤ m)
    (hN : 2 * m ≤ N) (h : M22) : hm ε N β h ≤ gm ε β m h + gm ε β m (swp h) := by
  have g1 := gm_nonneg' ε β m hβ h
  have g2 := gm_nonneg' ε β m hβ (swp h)
  by_cases hd : dt h = 0
  · have : hm ε N β h = 0 := by
      unfold hm
      rw [hd, Real.zero_rpow (by linarith)]
      simp
    rw [this]
    exact add_nonneg g1 g2
  by_cases hv : ‖h 1 0‖ ≤ ‖h 0 0‖
  · have := one_region ε β m N hε hβ hm' hN h hv hd
    linarith
  · have hv' : ‖(swp h) 1 0‖ ≤ ‖(swp h) 0 0‖ := by
      have : ‖h 0 0‖ ≤ ‖h 1 0‖ := (not_le.1 hv).le
      simpa [swp] using this
    have := one_region ε β m N hε hβ hm' hN (swp h) hv' (by rw [dt_swp]; exact hd)
    rw [hm_swp] at this
    linarith

end GlobalTheory.CompanionTheory.MajC
