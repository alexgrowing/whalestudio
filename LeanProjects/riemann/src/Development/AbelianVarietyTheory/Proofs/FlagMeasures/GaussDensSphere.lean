import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Sphere

private theorem norm_toLp_eq_sqrt_sum_norm_sq (n : ℕ) (y : Fin (n + 1) → ℂ) :
    ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin (n + 1)))‖ = Real.sqrt (∑ i, ‖y i‖ ^ 2) := by
  simp [EuclideanSpace.norm_eq]

private theorem volume_complex_unit_ball_toReal (n : ℕ) :
    (volume {y : Fin (n + 1) → ℂ | Real.sqrt (∑ i, ‖y i‖ ^ 2) < 1}).toReal =
      Real.pi ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hset : {y : Fin (n + 1) → ℂ | Real.sqrt (∑ i, ‖y i‖ ^ 2) < 1} =
      {y : Fin (n + 1) → ℂ | ∑ i, ‖y i‖ ^ (2 : ℝ) < 1} := by
    ext y
    simp only [Set.mem_setOf_eq, Real.rpow_two]
    rw [Real.sqrt_lt' one_pos, one_pow]
  rw [hset, Complex.volume_sum_rpow_lt_one (Fin (n + 1)) (by norm_num : (1 : ℝ) ≤ 2)]
  have h2 : (2 : ℝ) / 2 + 1 = 2 := by norm_num
  have h3 : 2 * (Fintype.card (Fin (n + 1)) : ℝ) / 2 + 1 = ((n + 1 : ℕ) : ℝ) + 1 := by
    simp only [Fintype.card_fin]; push_cast; ring
  rw [h2, h3, Real.Gamma_two, Real.Gamma_nat_eq_factorial, mul_one, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

theorem integral_radial (n : ℕ) (f : ℝ → ℝ) :
    ∫ y : Fin (n + 1) → ℂ, f (Real.sqrt (∑ i, ‖y i‖ ^ 2)) =
      2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) * ∫ r in Set.Ioi (0 : ℝ), r ^ (2 * n + 1) * f r := by

  let e := MeasurableEquiv.toLp 2 (Fin (n + 1) → ℂ)
  let μ : Measure (EuclideanSpace ℂ (Fin (n + 1))) := (volume : Measure (Fin (n + 1) → ℂ)).map e
  haveI : μ.IsAddHaarMeasure := by
    have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℂ)).symm.isAddHaarMeasure_map
      (volume : Measure (Fin (n + 1) → ℂ))
    exact h
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin (n + 1))) = 2 * (n + 1) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hball : μ.real (Metric.ball 0 1) = Real.pi ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    rw [Measure.real, MeasurableEquiv.map_apply, ← volume_complex_unit_ball_toReal n]
    congr 2
    ext y
    simp [e, norm_toLp_eq_sqrt_sum_norm_sq]
  have key := integral_fun_norm_addHaar μ f
  rw [integral_map_equiv] at key
  simp only [e, MeasurableEquiv.toLp_apply, norm_toLp_eq_sqrt_sum_norm_sq] at key
  rw [key, hdim, hball, show 2 * (n + 1) - 1 = 2 * n + 1 by omega, nsmul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  rw [Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem ball_integral (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ y in {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}, gauss y =
      2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) *
        ∫ r in (0 : ℝ)..Real.sqrt t, r ^ (2 * n + 1) * Real.exp (-r ^ 2) := by
  have hq (y : Fin (n + 1) → ℂ) : qEps (allPos (n + 1)) y = ∑ i, ‖y i‖ ^ 2 := by
    simp [qEps, allPos]
  have hmeas : MeasurableSet {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t} := by
    simp only [hq]
    exact measurableSet_le (by fun_prop) measurable_const

  have hind : {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}.indicator gauss =
      fun y => (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2))
        (Real.sqrt (∑ i, ‖y i‖ ^ 2)) := by
    funext y
    have hs : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
    by_cases hy : ∑ i, ‖y i‖ ^ 2 ≤ t
    · have hy' : Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ Real.sqrt t := Real.sqrt_le_sqrt hy
      rw [Set.indicator_of_mem (by simpa [hq] using hy), Set.indicator_of_mem (show Real.sqrt (∑ i, ‖y i‖ ^ 2) ∈ Set.Iic (Real.sqrt t) from hy'),
        Real.sq_sqrt hs, gauss]
    · have hy' : ¬ Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ Real.sqrt t := by
        intro h
        exact hy ((Real.sqrt_le_sqrt_iff ht.le).mp h)
      rw [Set.indicator_of_notMem (by simpa [hq] using hy), Set.indicator_of_notMem (show Real.sqrt (∑ i, ‖y i‖ ^ 2) ∉ Set.Iic (Real.sqrt t) from hy')]
  rw [← integral_indicator hmeas, hind,
    integral_radial n ((Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2))),
    intervalIntegral.integral_of_le (Real.sqrt_nonneg t)]
  congr 1
  have hfun : (fun r : ℝ => r ^ (2 * n + 1) *
      (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) r) =
      (Set.Iic (Real.sqrt t)).indicator (fun r => r ^ (2 * n + 1) * Real.exp (-r ^ 2)) := by
    funext r
    by_cases hr : r ∈ Set.Iic (Real.sqrt t)
    · simp [Set.indicator_of_mem hr]
    · simp [Set.indicator_of_notMem hr]
  rw [hfun, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]

theorem gaussDens_sphere (n : ℕ) :
    gaussDens (allPos (n + 1)) 1 = Real.pi ^ (n + 1) * Real.exp (-1) / (n.factorial : ℝ) := by
  set C : ℝ := 2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) with hC
  set h : ℝ → ℝ := fun r => r ^ (2 * n + 1) * Real.exp (-r ^ 2) with hh

  have hF : (fun t : ℝ => ∫ y in {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}, gauss y) =ᶠ[nhds 1]
      fun t => C * ∫ r in (0 : ℝ)..Real.sqrt t, h r := by
    filter_upwards [lt_mem_nhds one_pos] with t ht using ball_integral n ht
  have hcont : Continuous h := by rw [hh]; fun_prop
  have h1 := (hcont.integral_hasStrictDerivAt 0 (Real.sqrt 1)).hasDerivAt
  have h2 := Real.hasDerivAt_sqrt (one_ne_zero : (1 : ℝ) ≠ 0)
  have hd := (h1.comp (1 : ℝ) h2).const_mul C
  rw [gaussDens]
  refine (hF.deriv_eq.trans hd.deriv).trans ?_
  simp only [hh, hC, Real.sqrt_one, one_pow, one_mul]
  field_simp
  try ring

end GlobalTheory.GaussMean.Sphere
