import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LogIntSt

open MeasureTheory Set

namespace ReciprocityTheory.AnForm.A

theorem locallyIntegrable_comp_eval_fin {D : ℕ} (i : Fin D) {g : ℂ → ℝ}
    (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun z : Fin D → ℂ => g (z i)) volume := by
  classical
  intro x
  have hmeas : MeasurableSet (Set.pi Set.univ (fun j => Metric.closedBall (x j) (1 : ℝ))) :=
    MeasurableSet.univ_pi (fun j => measurableSet_closedBall)
  refine ⟨Set.pi Set.univ (fun j => Metric.closedBall (x j) 1),
    set_pi_mem_nhds Set.finite_univ (fun j _ => Metric.closedBall_mem_nhds (x j) one_pos), ?_⟩
  rw [← integrable_indicator_iff hmeas]
  have hf : ∀ j : Fin D, Integrable (fun w : ℂ => if j = i then (Metric.closedBall (x j) 1).indicator g w
      else (Metric.closedBall (x j) 1).indicator (fun _ => (1 : ℝ)) w) volume := by
    intro j
    split_ifs
    · exact (integrable_indicator_iff measurableSet_closedBall).mpr
        (hg.integrableOn_isCompact (isCompact_closedBall _ _))
    · exact (integrable_indicator_iff measurableSet_closedBall).mpr
        ((locallyIntegrable_const (1 : ℝ)).integrableOn_isCompact (isCompact_closedBall _ _))
  have hI := Integrable.fintype_prod (μ := fun _ : Fin D => (volume : Measure ℂ)) hf
  rw [volume_pi]
  refine hI.congr (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  by_cases hz : z ∈ Set.pi Set.univ (fun j => Metric.closedBall (x j) (1 : ℝ))
  · rw [Set.indicator_apply, if_pos hz]
    rw [Set.mem_univ_pi] at hz
    rw [Finset.prod_eq_single i]
    · simp [Set.indicator_apply, hz i]
    · intro j _ hj
      simp [hj, Set.indicator_apply, hz j]
    · simp
  · rw [Set.indicator_apply, if_neg hz]
    rw [Set.mem_univ_pi] at hz
    push_neg at hz
    obtain ⟨j, hj⟩ := hz
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by split_ifs <;> simp [Set.indicator_apply, hj])

theorem locallyIntegrable_comp_fst_real {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun p : ℝ × ℝ => g p.1) volume := by
  intro x
  refine ⟨Metric.closedBall x.1 1 ×ˢ Metric.closedBall x.2 1,
    prod_mem_nhds (Metric.closedBall_mem_nhds _ one_pos) (Metric.closedBall_mem_nhds _ one_pos), ?_⟩
  rw [← integrable_indicator_iff (measurableSet_closedBall.prod measurableSet_closedBall),
    Measure.volume_eq_prod]
  have h1 := (integrable_indicator_iff measurableSet_closedBall).mpr
    (hg.integrableOn_isCompact (isCompact_closedBall x.1 1))
  have h2 := (integrable_indicator_iff measurableSet_closedBall).mpr
    ((locallyIntegrable_const (μ := (volume : Measure ℝ)) (1 : ℝ)).integrableOn_isCompact
      (isCompact_closedBall x.2 1))
  refine (h1.mul_prod h2).congr (Filter.Eventually.of_forall fun p => ?_)
  by_cases ha : p.1 ∈ Metric.closedBall x.1 1 <;> by_cases hb : p.2 ∈ Metric.closedBall x.2 1 <;>
    simp [Set.indicator_apply, Set.mem_prod, ha, hb]

theorem locallyIntegrable_comp_snd_real {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun p : ℝ × ℝ => g p.2) volume := by
  intro x
  refine ⟨Metric.closedBall x.1 1 ×ˢ Metric.closedBall x.2 1,
    prod_mem_nhds (Metric.closedBall_mem_nhds _ one_pos) (Metric.closedBall_mem_nhds _ one_pos), ?_⟩
  rw [← integrable_indicator_iff (measurableSet_closedBall.prod measurableSet_closedBall),
    Measure.volume_eq_prod]
  have h1 := (integrable_indicator_iff measurableSet_closedBall).mpr
    ((locallyIntegrable_const (μ := (volume : Measure ℝ)) (1 : ℝ)).integrableOn_isCompact
      (isCompact_closedBall x.1 1))
  have h2 := (integrable_indicator_iff measurableSet_closedBall).mpr
    (hg.integrableOn_isCompact (isCompact_closedBall x.2 1))
  refine (h1.mul_prod h2).congr (Filter.Eventually.of_forall fun p => ?_)
  by_cases ha : p.1 ∈ Metric.closedBall x.1 1 <;> by_cases hb : p.2 ∈ Metric.closedBall x.2 1 <;>
    simp [Set.indicator_apply, Set.mem_prod, ha, hb]

theorem locallyIntegrable_real_log : LocallyIntegrable Real.log volume := by
  intro x
  refine ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    intervalIntegral.intervalIntegrable_log'

theorem locallyIntegrable_norm_real_log : LocallyIntegrable (fun x : ℝ => ‖Real.log x‖) volume := by
  intro x
  obtain ⟨s, hs, h⟩ := locallyIntegrable_real_log x
  exact ⟨s, hs, h.norm⟩

theorem norm_log_norm_le (z : ℂ) :
    ‖Real.log ‖z‖‖ ≤ ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖ := by
  simp only [Real.norm_eq_abs]
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hsum := Complex.norm_le_abs_re_add_abs_im z
  have a1 := abs_nonneg (Real.log z.re)
  have a2 := abs_nonneg (Real.log z.im)
  have a3 := abs_nonneg z.re
  have a4 := abs_nonneg z.im
  rcases le_or_gt 1 ‖z‖ with h1 | h1
  · have h2 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < ‖z‖)
    rw [abs_of_nonneg (Real.log_nonneg h1)]
    linarith
  · rcases eq_or_lt_of_le (norm_nonneg z) with h0 | h0
    · rw [← h0, Real.log_zero, abs_zero]
      positivity
    · rw [abs_of_neg (Real.log_neg h0 h1)]
      by_cases hr : z.re = 0
      · have hi : z.im ≠ 0 := by
          intro hi
          have hz : z = 0 := Complex.ext hr hi
          rw [hz, norm_zero] at h0
          exact lt_irrefl _ h0
        have h3 : Real.log |z.im| ≤ Real.log ‖z‖ := Real.log_le_log (abs_pos.mpr hi) him
        rw [Real.log_abs] at h3
        have h4 := neg_le_abs (Real.log z.im)
        linarith
      · have h3 : Real.log |z.re| ≤ Real.log ‖z‖ := Real.log_le_log (abs_pos.mpr hr) hre
        rw [Real.log_abs] at h3
        have h4 := neg_le_abs (Real.log z.re)
        linarith

theorem logNormLocIntC_thm : LogNormLocIntCStatement := by
  have hH : LocallyIntegrable
      (fun p : ℝ × ℝ => ‖Real.log p.1‖ + ‖Real.log p.2‖ + ‖p.1‖ + ‖p.2‖) volume :=
    (((locallyIntegrable_comp_fst_real locallyIntegrable_norm_real_log).add
      (locallyIntegrable_comp_snd_real locallyIntegrable_norm_real_log)).add
      (locallyIntegrable_comp_fst_real (continuous_norm (E := ℝ)).locallyIntegrable)).add
      (locallyIntegrable_comp_snd_real (continuous_norm (E := ℝ)).locallyIntegrable)
  have hG : LocallyIntegrable
      (fun z : ℂ => ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖) volume := by
    intro x
    obtain ⟨s, hs, hint⟩ := hH (Complex.measurableEquivRealProd x)
    have hcont : Continuous (Complex.measurableEquivRealProd : ℂ → ℝ × ℝ) := by
      show Continuous fun z : ℂ => (z.re, z.im)
      fun_prop
    refine ⟨Complex.measurableEquivRealProd ⁻¹' s, hcont.continuousAt.preimage_mem_nhds hs, ?_⟩
    exact (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hint
  refine hG.mono (Real.measurable_log.comp continuous_norm.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have h1 := norm_log_norm_le z
  have h2 : 0 ≤ ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖ := by positivity
  calc ‖Real.log ‖z‖‖ ≤ ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖ := h1
    _ = ‖‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖‖ := (Real.norm_of_nonneg h2).symm

theorem logCoordLocInt_thm : LogCoordLocIntStatement := fun D i => locallyIntegrable_comp_eval_fin i logNormLocIntC_thm

theorem logMonoLocInt_thm : LogMonoLocIntStatement := by
  intro D m
  exact locallyIntegrable_finset_sum (μ := volume) Finset.univ
    (f := fun i (z : Fin D → ℂ) => (m i : ℝ) * Real.log ‖z i‖)
    (fun i _ => (logCoordLocInt_thm D i).smul (m i : ℝ))

theorem logMonoTestInt_thm : LogMonoTestIntStatement := by
  intro D m f hf hfs
  exact (logMonoLocInt_thm D m).integrable_smul_left_of_hasCompactSupport hf hfs

theorem log_norm_prod_zpow_eq_logMono {D : ℕ} (m : Fin D → ℤ) (z : Fin D → ℂ)
    (hz : ∀ i, z i ≠ 0) : Real.log ‖∏ i, z i ^ m i‖ = logMono m z := by
  rw [norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hz i)))]
  unfold logMono
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_zpow, Real.log_zpow]

theorem logUnitMonoLocInt_thm : LogUnitMonoLocIntStatement := by
  intro D m U u hU hu hu0
  have hc : ContinuousOn (fun z => Real.log ‖u z‖) U :=
    (hu.continuousOn.norm).log (fun z hz => norm_ne_zero_iff.mpr (hu0 z hz))
  have h1 : LocallyIntegrableOn (fun z => Real.log ‖u z‖ + logMono m z) U volume :=
    (hc.locallyIntegrableOn hU.measurableSet).add ((logMonoLocInt_thm D m).locallyIntegrableOn U)
  have hnull : ∀ᵐ z ∂(volume : Measure (Fin D → ℂ)), ∀ i, z i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have hs : (volume : Measure (Fin D → ℂ))
        ((LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin D → ℂ)) :
          Set (Fin D → ℂ)) = 0 := by
      apply Measure.addHaar_submodule
      intro htop
      have h2 : (Pi.single i (1 : ℂ) : Fin D → ℂ) ∈
          LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ) := by
        rw [htop]
        exact Submodule.mem_top
      simp at h2
    have hset : {a : Fin D → ℂ | ¬ a i ≠ 0} =
        ((LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin D → ℂ)) :
          Set (Fin D → ℂ)) := by
      ext z
      simp
    rw [ae_iff, hset]
    exact hs
  rw [locallyIntegrableOn_iff hU.isLocallyClosed] at h1 ⊢
  intro K hKU hK
  refine (h1 K hKU hK).congr_fun_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' hK.isClosed.measurableSet]
  filter_upwards [hnull] with z hz hzK
  have hzU := hKU hzK
  show Real.log ‖u z‖ + logMono m z = Real.log ‖u z * ∏ i, z i ^ m i‖
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hu0 z hzU))
    (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hz i))),
    log_norm_prod_zpow_eq_logMono m z hz]

end ReciprocityTheory.AnForm.A
