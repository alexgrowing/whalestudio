import Mathlib

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Polynomial Real

def circPt (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * (t : ℂ))

lemma circPt_eq (t : ℝ) : circPt t = circleMap 0 1 (2 * π * t) := by
  rw [circleMap_zero, circPt]; push_cast; ring_nf

lemma norm_circPt (t : ℝ) : ‖circPt t‖ = 1 := by
  rw [circPt_eq, norm_circleMap_zero]; simp

instance isProbabilityMeasure_restrict_Ioc :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ⟨by simp⟩

lemma integrableOn_log_circ (p : ℂ[X]) :
    IntegrableOn (fun t => Real.log ‖p.eval (circPt t)‖) (Set.Ioc (0 : ℝ) 1) := by
  have h := (p.intervalIntegrable_mahlerMeasure).comp_mul_left (c := 2 * π) enorm_ne_top
    enorm_ne_top
  have h2 : IntervalIntegrable (fun t => Real.log ‖p.eval (circPt t)‖) volume 0 1 := by
    simp only [circPt_eq]
    convert h using 2 <;> simp
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h2

lemma integral_log_circ (p : ℂ[X]) :
    ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖p.eval (circPt t)‖ = p.logMahlerMeasure := by
  rw [← intervalIntegral.integral_of_le zero_le_one, logMahlerMeasure_def, circleAverage_def]
  simp only [circPt_eq]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.log ‖p.eval (circleMap 0 1 x)‖)
    (by positivity : (2 * π) ≠ 0)]
  simp

lemma log_norm_leadingCoeff_le (p : ℂ[X]) : Real.log ‖p.leadingCoeff‖ ≤ p.logMahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  rw [logMahlerMeasure_eq_log_MahlerMeasure]
  exact Real.log_le_log (norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp))
    (leadingCoeff_le_mahlerMeasure p)

lemma log_norm_coeff_top_le (p : ℂ[X]) (k : ℕ) (hk : p.coeff k ≠ 0)
    (htop : ∀ k', k < k' → p.coeff k' = 0) : Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure := by
  have hd : p.natDegree = k := by
    apply le_antisymm
    · exact natDegree_le_iff_coeff_eq_zero.mpr fun k' hk' => htop k' (by exact_mod_cast hk')
    · exact le_natDegree_of_ne_zero hk
  have := log_norm_leadingCoeff_le p
  rwa [leadingCoeff, hd] at this

lemma log_norm_coeff_bot_le (p : ℂ[X]) (k : ℕ) (hk : p.coeff k ≠ 0)
    (hbot : ∀ k', k' < k → p.coeff k' = 0) : Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure := by
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.mpr hbot
  have hp : p ≠ 0 := fun h => hk (by simp [h])
  have hq0 : q ≠ 0 := fun h => hp (by simp [hq, h])
  have hc : p.coeff k = q.coeff 0 := by
    rw [hq, coeff_X_pow_mul']; simp
  have hM : p.logMahlerMeasure = q.logMahlerMeasure := by
    rw [hq, logMahlerMeasure_mul_eq_add_logMahlerMeasure (by rw [← hq]; exact hp),
      X_pow_eq_monomial, logMahlerMeasure_monomial]
    simp
  rw [hc, hM, logMahlerMeasure_eq_log_MahlerMeasure]
  rw [hc] at hk
  apply Real.log_le_log (norm_pos_iff.mpr hk)
  simpa using norm_coeff_le_choose_mul_mahlerMeasure 0 q

lemma circPt_injOn : Set.InjOn circPt (Set.Ioc (0 : ℝ) 1) := by
  intro a ha b hb h
  simp only [circPt_eq] at h
  have hinj := injOn_circleMap_of_abs_sub_le (c := (0 : ℂ)) (R := 1) one_ne_zero
    (a := 0) (b := 2 * π) (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)])
  rw [Set.uIoc_of_le (by positivity)] at hinj
  have : 2 * π * a = 2 * π * b := by
    apply hinj
    · constructor <;> nlinarith [ha.1, ha.2, pi_pos]
    · constructor <;> nlinarith [hb.1, hb.2, pi_pos]
    · exact h
  have hpi : (2 * π) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi this

lemma zero_set_circ_null (p : ℂ[X]) (hp : p ≠ 0) :
    volume.restrict (Set.Ioc (0 : ℝ) 1) {t | p.eval (circPt t) = 0} = 0 := by
  rw [Measure.restrict_apply' measurableSet_Ioc]
  apply Set.Finite.measure_zero _ volume
  apply Set.Finite.of_finite_image (f := circPt) _ (circPt_injOn.mono fun _ h => h.2)
  apply p.roots.finite_toSet.subset
  rintro _ ⟨t, ⟨ht, _⟩, rfl⟩
  simpa [mem_roots hp] using ht

end ReciprocityTheory.MultiplicativeHeights
