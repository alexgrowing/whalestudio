import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLaplacianDecayZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian MeasureTheory Filter Topology

theorem LaplacianDecayZero.integral_line_eq_zero (v : ℂ → ℝ)
    (hdiff : Differentiable ℝ (fderiv ℝ v))
    (hlim : Tendsto (fderiv ℝ v) (cocompact ℂ) (𝓝 0)) (w e : ℂ) (he : ‖e‖ = 1) :
    ∫ t : ℝ, fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e = 0 := by
  have hγd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w + (s : ℂ) * e) e t := by
    intro t
    have := (((hasDerivAt_id t).ofReal_comp).mul_const e).const_add w
    simpa using this
  have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ v (w + (s : ℂ) * e) e)
      (fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e) t := by
    intro t
    have h1 := ((hdiff (w + (t : ℂ) * e)).hasFDerivAt).comp_hasDerivAt t (hγd t)
    have h2 := (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasDerivAt t h1
    exact h2
  have hiso : Isometry (fun s : ℝ => w + (s : ℂ) * e) := by
    refine Isometry.of_dist_eq fun s t => ?_
    rw [dist_eq_norm, dist_eq_norm,
      show w + (s : ℂ) * e - (w + (t : ℂ) * e) = ((s - t : ℝ) : ℂ) * e by push_cast; ring,
      norm_mul, he, mul_one, Complex.norm_real]
  have hcoc : Tendsto (fun s : ℝ => w + (s : ℂ) * e) (cocompact ℝ) (cocompact ℂ) :=
    hiso.isClosedEmbedding.tendsto_cocompact
  have hlim' : Tendsto (fun s : ℝ => fderiv ℝ v (w + (s : ℂ) * e) e) (cocompact ℝ) (𝓝 0) := by
    have := ((ContinuousLinearMap.apply ℝ ℝ e).continuous.tendsto 0).comp (hlim.comp hcoc)
    exact this
  by_cases hint : Integrable (fun t : ℝ => fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e)
  · have := integral_of_hasDerivAt_of_tendsto hF hint (hlim'.mono_left atBot_le_cocompact)
      (hlim'.mono_left atTop_le_cocompact)
    simpa using this
  · exact integral_undef hint

theorem LaplacianDecayZero.proof : LaplacianDecayZero.Statement := by
  intro v C R₀ hv hdec
  have hD2c : Continuous (iteratedFDeriv ℝ 2 v) := hv.continuous_iteratedFDeriv le_rfl
  have hdiff : Differentiable ℝ (fderiv ℝ v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hlim : Tendsto (fderiv ℝ v) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn : Tendsto (fun y : ℂ => ‖y‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    have hc : Tendsto (fun y : ℂ => C / ‖y‖ ^ 2) (cocompact ℂ) (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hn)
    refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) ?_ hc
    filter_upwards [hn.eventually_gt_atTop R₀] with y hy
    exact (hdec y hy).1

  obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ Metric.closedBall (0 : ℂ) (max R₀ 1),
      ‖iteratedFDeriv ℝ 2 v y‖ ≤ M :=
    (isCompact_closedBall 0 (max R₀ 1)).exists_bound_of_continuousOn hD2c.continuousOn
  have hR1 : (1 : ℝ) ≤ max R₀ 1 := le_max_right _ _
  have hMR : 0 ≤ |M| * (1 + max R₀ 1) ^ 3 :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) _)
  have hbound : ∀ y : ℂ, ‖iteratedFDeriv ℝ 2 v y‖ ≤
      (|M| * (1 + max R₀ 1) ^ 3 + 8 * |C|) * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
    intro y
    have hpos : 0 < 1 + ‖y‖ := by positivity
    rw [Real.rpow_neg hpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    by_cases hy : ‖y‖ ≤ max R₀ 1
    · have h1 := hM y (by simpa using hy)
      have h2 : (1 + ‖y‖) ^ 3 ≤ (1 + max R₀ 1) ^ 3 := by gcongr
      calc ‖iteratedFDeriv ℝ 2 v y‖ * (1 + ‖y‖) ^ 3 ≤ |M| * (1 + max R₀ 1) ^ 3 :=
            mul_le_mul (h1.trans (le_abs_self M)) h2 (by positivity) (abs_nonneg M)
        _ ≤ _ := by linarith [abs_nonneg C]
    · push Not at hy
      have hR0 : R₀ < ‖y‖ := lt_of_le_of_lt (le_max_left _ _) hy
      have hy1 : 1 < ‖y‖ := lt_of_le_of_lt hR1 hy
      have h1 := (hdec y hR0).2
      have h3 : ‖iteratedFDeriv ℝ 2 v y‖ * ‖y‖ ^ 3 ≤ |C| := by
        rw [le_div_iff₀ (by positivity)] at h1
        exact h1.trans (le_abs_self C)
      have h4 : (1 + ‖y‖) ^ 3 ≤ 8 * ‖y‖ ^ 3 := by
        calc (1 + ‖y‖) ^ 3 ≤ (2 * ‖y‖) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
          _ = 8 * ‖y‖ ^ 3 := by ring
      calc ‖iteratedFDeriv ℝ 2 v y‖ * (1 + ‖y‖) ^ 3
          ≤ ‖iteratedFDeriv ℝ 2 v y‖ * (8 * ‖y‖ ^ 3) := by gcongr
        _ = 8 * (‖iteratedFDeriv ℝ 2 v y‖ * ‖y‖ ^ 3) := by ring
        _ ≤ 8 * |C| := by gcongr
        _ ≤ _ := by linarith
  have hK : Integrable (fun y : ℂ =>
      (|M| * (1 + max R₀ 1) ^ 3 + 8 * |C|) * (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)).const_mul _

  have hpart : ∀ e : ℂ, ‖e‖ = 1 → Integrable (fun y => iteratedFDeriv ℝ 2 v y ![e, e]) := by
    intro e he
    refine hK.mono' ((continuous_eval_const (![e, e] : Fin 2 → ℂ)).comp hD2c).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    calc ‖iteratedFDeriv ℝ 2 v y ![e, e]‖
        ≤ ‖iteratedFDeriv ℝ 2 v y‖ * ∏ i, ‖(![e, e] : Fin 2 → ℂ) i‖ :=
          (iteratedFDeriv ℝ 2 v y).le_opNorm _
      _ = ‖iteratedFDeriv ℝ 2 v y‖ := by simp [Fin.prod_univ_two, he]
      _ ≤ _ := hbound y
  have hform : ∀ y e : ℂ, iteratedFDeriv ℝ 2 v y ![e, e] = fderiv ℝ (fderiv ℝ v) y e e := by
    intro y e
    rw [iteratedFDeriv_two_apply]
    rfl
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hemb := Complex.measurableEquivRealProd.symm.measurableEmbedding

  have htr : ∀ e : ℂ, ‖e‖ = 1 →
      (∫ y, iteratedFDeriv ℝ 2 v y ![e, e]) =
        ∫ p : ℝ × ℝ, iteratedFDeriv ℝ 2 v (Complex.measurableEquivRealProd.symm p) ![e, e] ∧
      Integrable (fun p : ℝ × ℝ =>
        iteratedFDeriv ℝ 2 v (Complex.measurableEquivRealProd.symm p) ![e, e])
        (volume.prod volume) := by
    intro e he
    exact ⟨(hmp.integral_comp hemb _).symm, (hmp.integrable_comp_emb hemb).mpr (hpart e he)⟩
  have hz1 : ∫ y, iteratedFDeriv ℝ 2 v y ![1, 1] = 0 := by
    obtain ⟨h1, h2⟩ := htr 1 (by simp)
    rw [h1, Measure.volume_eq_prod, integral_prod_symm _ h2]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun b => ?_)
    have := LaplacianDecayZero.integral_line_eq_zero v hdiff hlim ((b : ℂ) * Complex.I) 1 (by simp)
    simp only [Pi.zero_apply]
    rw [← this]
    congr 1
    ext x
    rw [hform, show Complex.measurableEquivRealProd.symm (x, b) = (b : ℂ) * Complex.I + (x : ℂ) * 1 from
      Complex.ext (by simp) (by simp)]
  have hzI : ∫ y, iteratedFDeriv ℝ 2 v y ![Complex.I, Complex.I] = 0 := by
    obtain ⟨h1, h2⟩ := htr Complex.I (by simp)
    rw [h1, Measure.volume_eq_prod, integral_prod _ h2]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun a => ?_)
    have := LaplacianDecayZero.integral_line_eq_zero v hdiff hlim (a : ℂ) Complex.I (by simp)
    simp only [Pi.zero_apply]
    rw [← this]
    congr 1
    ext t
    rw [hform, show Complex.measurableEquivRealProd.symm (a, t) = (a : ℂ) + (t : ℂ) * Complex.I from
      Complex.ext (by simp) (by simp)]
  have hΔ := laplacian_eq_iteratedFDeriv_complexPlane v
  have h1 := hpart 1 (by simp)
  have hI := hpart Complex.I (by simp)
  refine ⟨?_, ?_⟩
  · rw [hΔ]
    exact h1.add hI
  · rw [hΔ, integral_add h1 hI, hz1, hzI, add_zero]

end GroundTheory.Heights₂.Heights.LowerBoundFree
