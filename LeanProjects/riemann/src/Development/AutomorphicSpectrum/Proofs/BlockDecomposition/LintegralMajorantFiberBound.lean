import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern

noncomputable section

open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B

namespace GlobalTheory.CompanionTheory.MajC.TB

theorem gain_le {ε A D E T : ℝ} {N : ℕ} (hε : 0 < ε) (hN : 2 * ε ≤ N) (hA : 0 < A) (hD : 0 < D)
    (hE : 0 < E) (hT : 0 < T) :
    (T * E / (A + T * E)) ^ N * ((1 + T / (D * E)) ^ N)⁻¹ ≤
      (D * E ^ 2 / A) ^ ε * min ((T / √(A * D)) ^ (2 * ε)) ((√(A * D) / T) ^ (2 * ε)) := by
  have hAD : 0 < A * D := mul_pos hA hD
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, T₀ = √(A * D) := ⟨_, rfl⟩
  rw [← hT₀]
  have hT₀p : 0 < T₀ := hT₀ ▸ Real.sqrt_pos.mpr hAD
  have hsq : T₀ ^ 2 = A * D := by rw [hT₀]; exact Real.sq_sqrt hAD.le
  have hTE : 0 < T * E := mul_pos hT hE
  have hs : (0 : ℝ) ≤ 2 * ε := by positivity
  have hc : 0 < D * E ^ 2 / A := by positivity

  obtain ⟨x, hx⟩ : ∃ x, x = T * E / (A + T * E) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one (by positivity)]; linarith
  have hxA : x ≤ T * E / A := by
    rw [hx]; exact div_le_div_of_nonneg_left hTE.le hA (by linarith)
  have e1 : (T * E / A) ^ (2 * ε) = (D * E ^ 2 / A) ^ ε * (T / T₀) ^ (2 * ε) := by
    rw [Real.rpow_mul (by positivity), Real.rpow_mul (by positivity), Real.rpow_two, Real.rpow_two,
      ← Real.mul_rpow hc.le (by positivity)]
    congr 1
    rw [div_pow, div_pow, hsq]
    field_simp
  have hxN : x ^ N ≤ (D * E ^ 2 / A) ^ ε * (T / T₀) ^ (2 * ε) := by
    rw [← e1, ← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hN).trans
      (Real.rpow_le_rpow hx0.le hxA hs)
  have hxN1 : x ^ N ≤ 1 := pow_le_one₀ hx0.le hx1

  obtain ⟨w, hw⟩ : ∃ w, w = T / (D * E) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have e2 : (w⁻¹) ^ (2 * ε) = (D * E ^ 2 / A) ^ ε * (T₀ / T) ^ (2 * ε) := by
    rw [Real.rpow_mul (by positivity), Real.rpow_mul (by positivity), Real.rpow_two, Real.rpow_two,
      ← Real.mul_rpow hc.le (by positivity)]
    congr 1
    rw [hw, div_pow, hsq, inv_pow, div_pow, mul_pow]
    field_simp
  have hwN : ((1 + w) ^ N)⁻¹ ≤ (D * E ^ 2 / A) ^ ε * (T₀ / T) ^ (2 * ε) := by
    rw [← e2, Real.inv_rpow hw0.le]
    apply inv_anti₀ (Real.rpow_pos_of_pos hw0 _)
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow hw0.le (by linarith) hs).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hN)
  have hwN1 : ((1 + w) ^ N)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hwN0 : 0 ≤ ((1 + w) ^ N)⁻¹ := by positivity
  rw [← hx, ← hw, mul_min_of_nonneg _ _ (Real.rpow_nonneg hc.le _)]
  apply le_min
  · exact (mul_le_of_le_one_right (by positivity) hwN1).trans hxN
  · exact (mul_le_of_le_one_left hwN0 hxN1).trans hwN

theorem const_eq {ε A D E : ℝ} (hA : 0 < A) (hD : 0 < D) (hE : 0 < E) :
    (D ^ 2 * E ^ 2)⁻¹ * (D * E ^ 2 / A) ^ ε = A ^ (-ε) * D ^ (-2 + ε) * E ^ (-2 + 2 * ε) := by
  rw [Real.rpow_add hD, Real.rpow_add hE, Real.rpow_neg hA.le, Real.rpow_neg hD.le,
    Real.rpow_neg hE.le, Real.rpow_two, Real.rpow_two, Real.div_rpow (by positivity) hA.le,
    Real.mul_rpow hD.le (by positivity), Real.rpow_mul hE.le, Real.rpow_two]
  have := (Real.rpow_pos_of_pos hA ε).ne'
  field_simp

theorem jm_le_kern {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 2 * ε ≤ N) (h : M22) (a b t : ℂ) (ha : a ≠ 0)
    (hD : 0 < dt h) (hE : 0 < ‖eta h‖) :
    jm N h t a b ≤ (dt h ^ 2 * ‖eta h‖ ^ 2)⁻¹ * (dt h * ‖eta h‖ ^ 2 / ‖a‖) ^ ε *
        ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ * kern (2 * ε) (√(‖a‖ * dt h)) t := by
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  by_cases ht : t = 0
  · subst ht
    simp [jm, kern]
  have hT : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have key := gain_le (T := ‖t‖) hε hN hA hD hE hT
  have hP : 0 ≤ ((1 + ‖h‖) ^ N)⁻¹ := by positivity
  have hQ : 0 ≤ ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ := by positivity
  have hI : 0 ≤ (dt h ^ 2 * ‖eta h‖ ^ 2)⁻¹ * (‖t‖ ^ 2)⁻¹ * ((1 + ‖h‖) ^ N)⁻¹ *
      ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left key hI
  calc jm N h t a b = (dt h ^ 2 * ‖eta h‖ ^ 2)⁻¹ * (‖t‖ ^ 2)⁻¹ * ((1 + ‖h‖) ^ N)⁻¹ *
      ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ * ((‖t‖ * ‖eta h‖ / (‖a‖ + ‖t‖ * ‖eta h‖)) ^ N *
        ((1 + ‖t‖ / (dt h * ‖eta h‖)) ^ N)⁻¹) := by
        simp only [jm, dt, mul_inv]; ring
    _ ≤ _ := this
    _ = _ := by simp only [kern]; ring

theorem lintegral_jm_le : ∀ (ε K : ℝ), 0 < ε → 0 ≤ K →
    (∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern (2 * ε) T₀ z) ≤ ENNReal.ofReal K) →
    ∀ N : ℕ, 2 * ε ≤ N → ∀ (h : M22) (a b : ℂ), a ≠ 0 → 0 < dt h → 0 < ‖eta h‖ →
    ∫⁻ t : ℂ, ENNReal.ofReal (jm N h t a b) ≤
      ENNReal.ofReal (K * ‖a‖ ^ (-ε) * dt h ^ (-2 + ε) * ‖eta h‖ ^ (-2 + 2 * ε) *
        ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹) := by
  intro ε K hε hK hker N hN h a b ha hD hE
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨C, hC⟩ : ∃ C, C = (dt h ^ 2 * ‖eta h‖ ^ 2)⁻¹ * (dt h * ‖eta h‖ ^ 2 / ‖a‖) ^ ε *
      ((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖b‖ * ‖eta h‖) ^ N)⁻¹ := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    have : 0 ≤ (dt h * ‖eta h‖ ^ 2 / ‖a‖) ^ ε := Real.rpow_nonneg (by positivity) _
    positivity
  have hT₀ : 0 < √(‖a‖ * dt h) := Real.sqrt_pos.mpr (mul_pos hA hD)
  calc ∫⁻ t : ℂ, ENNReal.ofReal (jm N h t a b)
      ≤ ∫⁻ t : ℂ, ENNReal.ofReal C * ENNReal.ofReal (kern (2 * ε) (√(‖a‖ * dt h)) t) := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_mul hC0, hC]
        exact ENNReal.ofReal_le_ofReal (jm_le_kern hε hN h a b t ha hD hE)
    _ = ENNReal.ofReal C * ∫⁻ t : ℂ, ENNReal.ofReal (kern (2 * ε) (√(‖a‖ * dt h)) t) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal K := by gcongr; exact hker _ hT₀
    _ = ENNReal.ofReal (C * K) := (ENNReal.ofReal_mul hC0).symm
    _ = _ := by
        congr 1
        rw [hC, const_eq hA hD hE]
        ring

end GlobalTheory.CompanionTheory.MajC.TB
