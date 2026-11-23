import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFG

open MeasureTheory
open scoped ContDiff Convolution

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

private theorem parameter_smooth_lemma {Pm X W : Type} [NormedAddCommGroup Pm] [NormedSpace ℝ Pm]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (h : Pm → X → W) (s : Set Pm) (K : Set X) (hs : IsOpen s) (hK : IsCompact K)
    (hv : ∀ p ∈ s, ∀ x ∉ K, h p x = 0)
    (hh : ContDiffOn ℝ ∞ (fun q : Pm × X => h q.1 q.2) (s ×ˢ Set.univ)) :
    (∀ p ∈ s, ∀ x ∉ K, (fderiv ℝ (fun q : Pm × X => h q.1 q.2) (p, x)).comp
        (ContinuousLinearMap.inl ℝ Pm X) = 0) ∧
    ContDiffOn ℝ ∞ (fun q : Pm × X => (fderiv ℝ (fun q : Pm × X => h q.1 q.2) (q.1, q.2)).comp
        (ContinuousLinearMap.inl ℝ Pm X)) (s ×ˢ Set.univ) ∧
    ∀ p ∈ s, ∀ x, HasFDerivAt (fun p' => h p' x)
      ((fderiv ℝ (fun q : Pm × X => h q.1 q.2) (p, x)).comp (ContinuousLinearMap.inl ℝ Pm X)) p := by
  have hO : IsOpen (s ×ˢ (Set.univ : Set X)) := hs.prod isOpen_univ
  refine ⟨?_, ?_, ?_⟩
  · intro p hp x hx
    have hU : IsOpen (s ×ˢ Kᶜ) := hs.prod hK.isClosed.isOpen_compl
    have hz : (fun q : Pm × X => h q.1 q.2) =ᶠ[nhds (p, x)] fun _ => 0 := by
      filter_upwards [hU.mem_nhds ⟨hp, hx⟩] with q hq
      exact hv q.1 hq.1 q.2 hq.2
    rw [hz.fderiv_eq]
    simp
  · have h1 : ContDiffOn ℝ ∞ (fun q => fderiv ℝ (fun q : Pm × X => h q.1 q.2) q) (s ×ˢ Set.univ) :=
      hh.fderiv_of_isOpen hO (by simp)
    exact h1.clm_comp contDiffOn_const
  · intro p hp x
    have hd : DifferentiableAt ℝ (fun q : Pm × X => h q.1 q.2) (p, x) :=
      (hh.contDiffAt (hO.mem_nhds ⟨hp, trivial⟩)).differentiableAt (by simp)
    have hl : HasFDerivAt (fun e : Pm => (e, x)) (ContinuousLinearMap.inl ℝ Pm X) p :=
      hasFDerivAt_prodMk_left (𝕜 := ℝ) p x
    exact HasFDerivAt.comp (x := p) hd.hasFDerivAt hl

private theorem parameter_smooth_lemma_2 {Pm X W : Type} [NormedAddCommGroup Pm] [NormedSpace ℝ Pm]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
    [BorelSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (h : Pm → X → W) (D : Pm → X → (Pm →L[ℝ] W)) (s : Set Pm) (K : Set X)
    (hs : IsOpen s) (hK : IsCompact K)
    (hv : ∀ p ∈ s, ∀ x ∉ K, h p x = 0) (hDv : ∀ p ∈ s, ∀ x ∉ K, D p x = 0)
    (hc : ContinuousOn (fun q : Pm × X => h q.1 q.2) (s ×ˢ Set.univ))
    (hDc : ContinuousOn (fun q : Pm × X => D q.1 q.2) (s ×ˢ Set.univ))
    (hD : ∀ p ∈ s, ∀ x, HasFDerivAt (fun p' => h p' x) (D p x) p)
    (p0 : Pm) (hp0 : p0 ∈ s) :
    HasFDerivAt (fun p => ∫ x, h p x ∂μ) (∫ x, D p0 x ∂μ) p0 := by
  have hO : IsOpen (s ×ˢ (Set.univ : Set X)) := hs.prod isOpen_univ
  have hcont : ∀ p ∈ s, Continuous (h p) := fun p hp =>
    hc.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, trivial⟩)
  have hDcont : ∀ p ∈ s, Continuous (D p) := fun p hp =>
    hDc.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, trivial⟩)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hDcont p0 hp0).continuousOn
  have hev : ∀ᶠ p in nhds p0, ∀ x ∈ K, ‖D p x‖ < C + 1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hca : ContinuousAt (fun q : Pm × X => D q.1 q.2) (p0, x) :=
      hDc.continuousAt (hO.mem_nhds ⟨hp0, trivial⟩)
    exact hca.norm.eventually (gt_mem_nhds (lt_of_le_of_lt (hC x hx) (lt_add_one C)))
  have hS : {p | p ∈ s ∧ ∀ x ∈ K, ‖D p x‖ < C + 1} ∈ nhds p0 :=
    Filter.inter_mem (hs.mem_nhds hp0) hev
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := K.indicator fun _ => C + 1) hS
    ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hs.mem_nhds hp0] with p hp
    exact (hcont p hp).aestronglyMeasurable
  · exact (hcont p0 hp0).integrable_of_hasCompactSupport (HasCompactSupport.intro hK (hv p0 hp0))
  · exact (hDcont p0 hp0).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x p hp => ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      exact (hp.2 x hx).le
    · rw [Set.indicator_of_notMem hx, hDv p hp.1 x hx, norm_zero]
  · exact (integrable_indicator_iff hK.isClosed.measurableSet).2
      (integrableOn_const hK.measure_lt_top.ne)
  · exact Filter.Eventually.of_forall fun x p hp => hD p hp.1 x

theorem parameter_smooth : ParamSmooth := by
  intro Pm X W _ _ _ _ _ _ _ _ _ μ _ h s K hs hK hv hh
  have key : ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (g : Pm → X → V),
      (∀ p ∈ s, ∀ x ∉ K, g p x = 0) →
      ContDiffOn ℝ ∞ (fun q : Pm × X => g q.1 q.2) (s ×ˢ Set.univ) →
      ContDiffOn ℝ n (fun p => ∫ x, g p x ∂μ) s := by
    intro n
    induction n with
    | zero =>
      intro V _ _ g hgv hg
      obtain ⟨hDv, hDs, hD⟩ := parameter_smooth_lemma g s K hs hK hgv hg
      have hdiff : DifferentiableOn ℝ (fun p => ∫ x, g p x ∂μ) s := fun p hp =>
        (parameter_smooth_lemma_2 μ g _ s K hs hK hgv hDv hg.continuousOn hDs.continuousOn hD p
          hp).differentiableAt.differentiableWithinAt
      exact contDiffOn_zero.2 hdiff.continuousOn
    | succ n ih =>
      intro V _ _ g hgv hg
      obtain ⟨hDv, hDs, hD⟩ := parameter_smooth_lemma g s K hs hK hgv hg
      have hder := fun p hp =>
        parameter_smooth_lemma_2 μ g _ s K hs hK hgv hDv hg.continuousOn hDs.continuousOn hD p hp
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs]
      refine ⟨fun p hp => (hder p hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact (ih (Pm →L[ℝ] V) (fun p x => (fderiv ℝ (fun q : Pm × X => g q.1 q.2) (p, x)).comp
        (ContinuousLinearMap.inl ℝ Pm X)) hDv hDs).congr fun p hp => (hder p hp).fderiv
  exact contDiffOn_infty.2 fun n => key n W h hv hh

end Formalism.FourierDecayAlt.P.CutSH.SFG
