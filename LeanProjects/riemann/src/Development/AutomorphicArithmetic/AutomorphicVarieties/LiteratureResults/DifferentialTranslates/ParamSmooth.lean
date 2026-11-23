import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

open Set MeasureTheory Metric Filter Topology
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem paramSmooth : ParamSmooth := by
  intro P F _ _ _ _ _ _ O S g hO hS hOS hg p₀ hp₀
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨u, v, hu, hv, hpu, hIv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := p₀))
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)) hS ((prod_mono (singleton_subset_iff.2 hp₀) subset_rfl).trans hOS)
  have hI : Icc (0 : ℝ) 1 = closedBall (1 / 2) (1 / 2) := by
    rw [Real.closedBall_eq_Icc]; norm_num
  obtain ⟨ε, hε, hεv⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_cthickening_subset_open hv hIv
  rw [hI, cthickening_closedBall hε.le (by norm_num)] at hεv
  let b : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, ε + 1 / 2, by norm_num, by linarith⟩
  have hbs : tsupport b = closedBall (1 / 2 : ℝ) (ε + 1 / 2) := b.tsupport_eq
  have hb0 : ∀ s, s ∉ closedBall (1 / 2 : ℝ) (ε + 1 / 2) → b s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport (by rwa [hbs])
  have hb1 : ∀ s ∈ Icc (0 : ℝ) 1, b s = 1 := fun s hs => b.one_of_mem_closedBall (by rwa [hI] at hs)
  let K : P × ℝ → F := fun q => b q.2 • g q
  have hK : ContDiffOn ℝ ∞ K (u ×ˢ univ) := by
    intro q hq
    apply ContDiffAt.contDiffWithinAt
    by_cases hqv : q.2 ∈ v
    · have h1 : ContDiffAt ℝ ∞ g q := hg.contDiffAt (hS.mem_nhds (huv ⟨hq.1, hqv⟩))
      have h2 : ContDiff ℝ ∞ (fun q : P × ℝ => b q.2) := b.contDiff.comp contDiff_snd
      exact h2.contDiffAt.smul h1
    · have hq2 : q.2 ∉ closedBall (1 / 2 : ℝ) (ε + 1 / 2) := fun h => hqv (hεv h)
      refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (isClosed_closedBall.isOpen_compl.mem_nhds hq2)] with q' hq'
      simp only [K, hb0 q'.2 hq', zero_smul]
  have hf : LocallyIntegrable ((Ioc (0 : ℝ) 1).indicator fun _ => (1 : ℝ)) volume :=
    ((integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))).locallyIntegrable
  have hgs : ∀ p, ∀ x, p ∈ u → x ∉ -closedBall (1 / 2 : ℝ) (ε + 1 / 2) →
      (fun z (y : ℝ) => K (z, -y)) p x = 0 := by
    intro p x _ hx
    have := hb0 (-x) (fun h => hx (Set.mem_neg.2 h))
    simp only [K, this, zero_smul]
  have hg' : ContDiffOn ℝ (⊤ : ℕ∞) (↿(fun z (y : ℝ) => K (z, -y))) (u ×ˢ Set.univ) := by
    have h1 : ContDiff ℝ ∞ (fun p : P × ℝ => (p.1, -p.2)) :=
      contDiff_fst.prodMk contDiff_snd.neg
    refine hK.comp h1.contDiffOn ?_
    rintro ⟨p, x⟩ ⟨hp, -⟩
    exact ⟨hp, Set.mem_univ _⟩
  have hv0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : P => (0 : ℝ)) u := contDiffOn_const
  have main := contDiffOn_convolution_right_with_param_comp (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) hv0 hu (isCompact_closedBall _ _).neg hgs hf hg'
  have fin : ContDiffOn ℝ ∞ (fun p => ∫ s in (0 : ℝ)..1, g (p, s)) u := by
    refine main.congr ?_
    intro z _
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub, neg_neg]
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ Ioc (0 : ℝ) 1
    · simp [Set.indicator_of_mem hw, K, hb1 w (Ioc_subset_Icc_self hw)]
    · simp [Set.indicator_of_notMem hw]
  exact fin.contDiffAt (hu.mem_nhds (hpu rfl))

end UpperTheory.V.Lit.Dr
