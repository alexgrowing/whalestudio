import Formalism.GaussValuationBounds.GaussUnit

noncomputable section

namespace Formalism.NOK

open scoped ENNReal

open IsDiscreteValuationRing in
theorem minLeGaussValAdd : GaussAdd := by
  intro O _ _ _ x f g
  refine le_iInf fun n => ?_
  have h1 : min (gaussV x f) (gaussV x g) ≤
      min ((((addVal O (PowerSeries.coeff n f) : ℕ∞)) : ℝ≥0∞) + ENNReal.ofReal (x * n))
        ((((addVal O (PowerSeries.coeff n g) : ℕ∞)) : ℝ≥0∞) + ENNReal.ofReal (x * n)) :=
    min_le_min (iInf_le _ n) (iInf_le _ n)
  refine h1.trans ?_
  rw [min_add_add_right, map_add]
  gcongr ?_ + _
  have h2 := addVal_add (R := O) (a := PowerSeries.coeff n f) (b := PowerSeries.coeff n g)
  rcases le_total (addVal O (PowerSeries.coeff n f)) (addVal O (PowerSeries.coeff n g)) with h | h
  · rw [min_eq_left (ENat.toENNReal_le.mpr h)]
    exact ENat.toENNReal_le.mpr (by rwa [min_eq_left h] at h2)
  · rw [min_eq_right (ENat.toENNReal_le.mpr h)]
    exact ENat.toENNReal_le.mpr (by rwa [min_eq_right h] at h2)

open IsDiscreteValuationRing in
theorem gaussValC : GaussC := by
  intro O _ _ _ x _ c
  refine le_antisymm ((iInf_le _ 0).trans (by simp)) (le_iInf fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [PowerSeries.coeff_C, if_neg hn.ne', addVal_zero]
    simp

open IsDiscreteValuationRing in
theorem gaussValUnit : GaussUnit := by
  intro O _ _ _ x _ u hu
  obtain ⟨w, hw⟩ := hu.map (PowerSeries.constantCoeff (R := O))
  refine le_antisymm ((iInf_le _ 0).trans ?_) (by simp)
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hw, addVal_eq_zero_of_unit]
  simp

open IsDiscreteValuationRing in
theorem gaussEis_true : GaussEis := by
  intro O _ _ _ ϖ hϖ x hx E N hN hE hdeg
  have hc : ∀ n, PowerSeries.coeff n (E : PowerSeries O) = E.coeff n := fun n => Polynomial.coeff_coe _ _
  have hv1 : addVal O ϖ = 1 := addVal_uniformizer hϖ
  have hlow : ∀ n, n < N → 1 ≤ addVal O (E.coeff n) := by
    intro n hn
    have hm : E.coeff n ∈ Ideal.span {ϖ} := hE.2 (by rw [hdeg]; exact hn)
    rw [Ideal.mem_span_singleton] at hm
    rw [← hv1]
    exact addVal_le_iff_dvd.mpr hm
  have h0 : addVal O (E.coeff 0) ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : 2 ≤ addVal O (E.coeff 0) := by
      have h6 := Order.add_one_le_of_lt h
      rwa [one_add_one_eq_two] at h6
    have h3 : addVal O (ϖ ^ 2) ≤ addVal O (E.coeff 0) := by
      rw [addVal_pow, hv1]
      simpa using h2
    apply hE.3
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact addVal_le_iff_dvd.mp h3
  have hN0 : addVal O (E.coeff N) = 0 := by
    have hl := hE.1
    rw [Polynomial.leadingCoeff, hdeg, Ideal.mem_span_singleton] at hl
    have h4 : addVal O (E.coeff N) < 1 := by
      rw [← hv1]
      exact lt_of_not_ge (fun h => hl (addVal_le_iff_dvd.mp h))
    exact ENat.lt_one_iff_eq_zero.mp h4
  have hmin : ENNReal.ofReal (min 1 (x * N)) = min 1 (ENNReal.ofReal (x * N)) := by
    rw [ENNReal.ofReal_mono.map_min, ENNReal.ofReal_one]
  unfold gaussV
  rw [hmin]
  refine le_antisymm (le_min ?_ ?_) (le_iInf fun n => ?_)
  · refine (iInf_le _ 0).trans ?_
    rw [hc]
    simp only [Nat.cast_zero, mul_zero, ENNReal.ofReal_zero, add_zero]
    have h5 := ENat.toENNReal_le.mpr h0
    simpa using h5
  · refine (iInf_le _ N).trans ?_
    rw [hc, hN0]
    simp
  · rw [hc]
    rcases lt_trichotomy n N with h | rfl | h
    · refine (min_le_left _ _).trans ?_
      refine le_trans ?_ le_self_add
      have h5 := ENat.toENNReal_le.mpr (hlow n h)
      simpa using h5
    · rw [hN0]
      simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact h), addVal_zero]
      simp

end Formalism.NOK
