import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

noncomputable section

open scoped ContDiff Topology
open Set MeasureTheory

namespace UpperTheory.V.Lit.Dr

theorem paramDeriv : ParamDeriv := by
  intro V F _ _ _ _ _ _ p W Φ hW hWp hΦ
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hdiff : DifferentiableOn ℝ Φ W := hΦ.differentiableOn (by simpa using h1)
  set G : V × ℝ → V →L[ℝ] F := fun z => (fderiv ℝ Φ z).comp (ContinuousLinearMap.inl ℝ V ℝ) with hG
  have hGc : ContinuousOn G W :=
    (hΦ.continuousOn_fderiv_of_isOpen hW h1).clm_comp continuousOn_const
  have hpart : ∀ z ∈ W, HasFDerivAt (fun x => Φ (x, z.2)) (G z) z.1 := by
    intro z hz
    have hz1 : HasFDerivAt Φ (fderiv ℝ Φ z) z :=
      ((hdiff z hz).differentiableAt (hW.mem_nhds hz)).hasFDerivAt
    exact hz1.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)
  have hI : ∀ t ∈ Set.uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  have hline : ∀ x : V, Continuous (fun t : ℝ => (x, t)) := fun x =>
    continuous_const.prodMk continuous_id
  obtain ⟨u, v, hu, hv, hpu, hIv, huv⟩ := generalized_tube_lemma isCompact_singleton
    isCompact_Icc hW (by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      simp only [mem_singleton_iff] at hx
      subst hx
      exact hWp t ht)
  obtain ⟨ε, εpos, hball⟩ := Metric.isOpen_iff.mp hu p (hpu rfl)
  have hε : 0 < ε / 2 := half_pos εpos
  have hKW : Metric.closedBall p (ε / 2) ×ˢ Icc (0 : ℝ) 1 ⊆ W := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact huv ⟨hball (Metric.closedBall_subset_ball (by linarith) hx), hIv ht⟩
  have hKc : IsCompact (Metric.closedBall p (ε / 2) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall p (ε / 2)).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hGc.mono hKW)
  have hpW : ∀ t ∈ Icc (0 : ℝ) 1, (p, t) ∈ W := hWp
  have hcont1 : ContinuousOn (fun t : ℝ => G (p, t)) (Icc 0 1) :=
    hGc.comp (hline p).continuousOn (fun t ht => hpW t ht)
  refine ⟨?_, ?_⟩
  · refine hcont1.congr ?_
    intro t ht
    exact (hpart (p, t) (hpW t ht)).fderiv
  · have hxW : ∀ x ∈ Metric.closedBall p (ε / 2), ∀ t ∈ Set.uIoc (0 : ℝ) 1, (x, t) ∈ W :=
      fun x hx t ht => hKW ⟨hx, hI t ht⟩
    have main := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume) (F := fun x t => Φ (x, t)) (F' := fun x t => G (x, t))
      (bound := fun _ => C) (s := Metric.closedBall p (ε / 2)) (a := 0) (b := 1)
      (Metric.closedBall_mem_nhds p hε)
      (by
        filter_upwards [Metric.closedBall_mem_nhds p hε] with x hx
        exact (hΦ.continuousOn.comp (hline x).continuousOn
          (fun t ht => hxW x hx t ht)).aestronglyMeasurable measurableSet_uIoc)
      (by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le zero_le_one]
        exact hΦ.continuousOn.comp (hline p).continuousOn (fun t ht => hpW t ht))
      ((hcont1.mono (fun t ht => hI t ht)).aestronglyMeasurable measurableSet_uIoc)
      (Filter.Eventually.of_forall fun t ht x hx => hC _ ⟨hx, hI t ht⟩)
      intervalIntegrable_const
      (Filter.Eventually.of_forall fun t ht x hx => hpart (x, t) (hxW x hx t ht))
    refine main.congr_fderiv ?_
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact ((hpart (p, t) (hpW t ht)).fderiv).symm

end UpperTheory.V.Lit.Dr
