import Mathlib
open MeasureTheory Set
open scoped ContDiff

namespace GlobalTheory

theorem contDiffOn_setIntegral_Icc_of_contDiffOn_param :
    ∀ (E ι : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] (O : Set E)
      (F : E × (ι → ℝ) → ℂ), IsOpen O → ContDiffOn ℝ ∞ F (O ×ˢ Set.univ) →
      ContDiffOn ℝ ∞ (fun v => ∫ x in Icc (0 : ι → ℝ) 1, F (v, x)) O := by
  intro E ι _ _ _ O F hO hF
  let χ : ContDiffBump (0 : ι → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let g : E → (ι → ℝ) → ℂ := fun p y => χ (-y) • F (p, -y)
  have hf : LocallyIntegrable ((Icc (0 : ι → ℝ) 1).indicator (fun _ => (1 : ℝ))) volume :=
    ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by simp [Real.volume_Icc_pi]) )).locallyIntegrable
  have hgs : ∀ p, ∀ y, p ∈ O → y ∉ Metric.closedBall (0 : ι → ℝ) 2 → g p y = 0 := by
    intro p y _ hy
    have h2 : χ (-y) = 0 := by
      apply Function.notMem_support.1
      rw [χ.support_eq]
      simp only [Metric.mem_ball, dist_zero_right, norm_neg]
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hy
      exact fun h => lt_asymm h hy
    simp [g, h2]
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (↿g) (O ×ˢ Set.univ) := by
    have h1 : ContDiff ℝ ∞ (fun p : E × (ι → ℝ) => (p.1, -p.2)) :=
      contDiff_fst.prodMk contDiff_snd.neg
    have hF' : ContDiffOn ℝ ∞ (fun p : E × (ι → ℝ) => F (p.1, -p.2)) (O ×ˢ Set.univ) := by
      refine hF.comp h1.contDiffOn ?_
      rintro ⟨p, x⟩ ⟨hp, -⟩
      exact ⟨hp, Set.mem_univ _⟩
    have hχ : ContDiffOn ℝ ∞ (fun p : E × (ι → ℝ) => χ (-p.2)) (O ×ˢ Set.univ) :=
      (χ.contDiff.comp contDiff_snd.neg).contDiffOn
    exact hχ.smul hF'
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : E => (0 : ι → ℝ)) O := contDiffOn_const
  have main := contDiffOn_convolution_right_with_param_comp (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) hv hO (isCompact_closedBall 0 2) hgs hf hg
  refine main.congr ?_
  intro v _
  rw [← integral_indicator measurableSet_Icc]
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub, neg_neg, g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Icc (0 : ι → ℝ) 1
  · have hχt : χ t = 1 := by
      apply χ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
      rw [Real.norm_eq_abs, abs_le]
      have h0 : (0 : ℝ) ≤ t i := ht.1 i
      exact ⟨by linarith, ht.2 i⟩
    simp [Set.indicator_of_mem ht, hχt]
  · simp [Set.indicator_of_notMem ht]

end GlobalTheory
