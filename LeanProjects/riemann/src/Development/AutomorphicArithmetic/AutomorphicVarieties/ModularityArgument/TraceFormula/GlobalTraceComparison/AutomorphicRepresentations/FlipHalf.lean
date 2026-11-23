import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory Filter Topology

private lemma flip_half (β : ℝ → ℝ) (hi : Integrable β) (h1 : ∫ t, β t = 1) (c : ℝ) :
    Integrable (fun s : ℝ => β (-(s + c) - s)) ∧ ∫ s : ℝ, β (-(s + c) - s) = 1 / 2 := by
  have e : ∀ s : ℝ, β (-(s + c) - s) = (fun y => β (y - c)) ((-2 : ℝ) * s) := by
    intro s
    show β _ = β _
    congr 1
    ring
  have hg : Integrable (fun y => β (y - c)) := hi.comp_sub_right c
  refine ⟨?_, ?_⟩
  · simp_rw [e]
    exact hg.comp_mul_left' (by norm_num)
  · simp_rw [e]
    rw [Measure.integral_comp_mul_left (fun y => β (y - c)) (-2 : ℝ),
      integral_sub_right_eq_self β c, h1]
    norm_num

private lemma flip_core {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z] (ν : Measure X) [SFinite ν]
    (μ : Measure Z) [SFinite μ] (l : X → ℝ) (l' : Z → ℝ) (F : ℝ → X → ℂ) (m : Z → ℂ) (d : X → ℝ)
    (hl : Measurable l) (hl' : Measurable l') (hF : Measurable (Function.uncurry F))
    (hm : Integrable m μ) (hd : Integrable d ν)
    (hb : ∀ s x, |s - l x| ≤ 1 → ‖F s x‖ ≤ d x)
    (hh : ∀ (s : ℝ) (u : ℝ → ℂ), Continuous u → HasCompactSupport u →
      ∫ x, F s x * u (l x) ∂ν = ∫ z, m z * u (-(s + l' z)) ∂μ)
    (β : ℝ → ℝ) (hc : Continuous β) (hs : HasCompactSupport β) (h0 : ∀ t, 0 ≤ β t)
    (h1 : ∫ t, β t = 1) (hr : ∀ t, β t ≠ 0 → |t| ≤ 1) :
    Integrable (fun x => ∫ s : ℝ, F s x * (β (l x - s) : ℂ)) ν ∧
      (∀ x, ‖∫ s : ℝ, F s x * (β (l x - s) : ℂ)‖ ≤ d x) ∧
      ∫ x, (∫ s : ℝ, F s x * (β (l x - s) : ℂ)) ∂ν = (∫ z, m z ∂μ) / 2 := by
  have hi : Integrable β := hc.integrable_of_hasCompactSupport hs
  have hd0 : ∀ x, 0 ≤ d x := fun x => (norm_nonneg _).trans (hb (l x) x (by simp))
  have hpt : ∀ x s, ‖F s x * (β (l x - s) : ℂ)‖ ≤ d x * β (l x - s) := by
    intro x s
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _)]
    by_cases h : β (l x - s) = 0
    · simp [h]
    · have := hr _ h
      rw [abs_sub_comm] at this
      exact mul_le_mul_of_nonneg_right (hb s x this) (h0 _)
  have hmeas : Measurable (fun p : X × ℝ => F p.2 p.1 * (β (l p.1 - p.2) : ℂ)) := by
    have a : Measurable (fun p : X × ℝ => F p.2 p.1) :=
      hF.comp (measurable_snd.prodMk measurable_fst)
    have b : Measurable (fun p : X × ℝ => β (l p.1 - p.2)) :=
      hc.measurable.comp ((hl.comp measurable_fst).sub measurable_snd)
    exact a.mul (Complex.measurable_ofReal.comp b)
  have hsec : ∀ x, Integrable (fun s : ℝ => F s x * (β (l x - s) : ℂ)) := by
    intro x
    have hmaj : Integrable (fun s : ℝ => d x * β (l x - s)) := (hi.comp_sub_left (l x)).const_mul _
    refine hmaj.mono' ?_ (Eventually.of_forall fun s => hpt x s)
    exact (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hle : ∀ x, ∫ s : ℝ, ‖F s x * (β (l x - s) : ℂ)‖ ≤ d x := by
    intro x
    have hmaj : Integrable (fun s : ℝ => d x * β (l x - s)) := (hi.comp_sub_left (l x)).const_mul _
    calc ∫ s : ℝ, ‖F s x * (β (l x - s) : ℂ)‖ ≤ ∫ s : ℝ, d x * β (l x - s) :=
          integral_mono (hsec x).norm hmaj (fun s => hpt x s)
      _ = d x := by
          rw [integral_const_mul, integral_sub_left_eq_self β volume (l x), h1, mul_one]
  have hprod : Integrable (fun p : X × ℝ => F p.2 p.1 * (β (l p.1 - p.2) : ℂ)) (ν.prod volume) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall hsec, ?_⟩
    refine hd.mono' hmeas.aestronglyMeasurable.norm.integral_prod_right' (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hle x
  refine ⟨hprod.integral_prod_left, fun x => (norm_integral_le_integral_norm _).trans (hle x), ?_⟩
  have hsw := integral_integral_swap (f := fun x (s : ℝ) => F s x * (β (l x - s) : ℂ)) hprod
  rw [hsw]
  have hstep : ∀ s : ℝ, ∫ x, F s x * (β (l x - s) : ℂ) ∂ν =
      ∫ z, m z * (β (-(s + l' z) - s) : ℂ) ∂μ := by
    intro s
    have hu : HasCompactSupport (fun t : ℝ => ((β (t - s) : ℝ) : ℂ)) := by
      have : HasCompactSupport (fun t : ℝ => β (t - s)) := hs.comp_homeomorph (Homeomorph.subRight s)
      exact this.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
    exact hh s (fun t => ((β (t - s) : ℝ) : ℂ)) (by fun_prop) hu
  simp_rw [hstep]
  have hmeas2 : AEStronglyMeasurable
      (fun p : ℝ × Z => m p.2 * (β (-(p.1 + l' p.2) - p.1) : ℂ)) ((volume : Measure ℝ).prod μ) := by
    have a : AEStronglyMeasurable (fun p : ℝ × Z => m p.2) ((volume : Measure ℝ).prod μ) :=
      hm.aestronglyMeasurable.comp_snd
    have b : Measurable (fun p : ℝ × Z => β (-(p.1 + l' p.2) - p.1)) :=
      hc.measurable.comp (((measurable_fst.add (hl'.comp measurable_snd)).neg).sub measurable_fst)
    exact a.mul (Complex.measurable_ofReal.comp b).aestronglyMeasurable
  have hnorm : ∀ z, ∫ s : ℝ, ‖m z * (β (-(s + l' z) - s) : ℂ)‖ = ‖m z‖ / 2 := by
    intro z
    have : ∀ s : ℝ, ‖m z * (β (-(s + l' z) - s) : ℂ)‖ = ‖m z‖ * β (-(s + l' z) - s) := by
      intro s
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _)]
    simp_rw [this]
    rw [integral_const_mul, (flip_half β hi h1 (l' z)).2]
    ring
  have hprod2 : Integrable (fun p : ℝ × Z => m p.2 * (β (-(p.1 + l' p.2) - p.1) : ℂ))
      ((volume : Measure ℝ).prod μ) := by
    rw [integrable_prod_iff' hmeas2]
    refine ⟨Eventually.of_forall fun z => ?_, ?_⟩
    · have := (flip_half β hi h1 (l' z)).1.ofReal (𝕜 := ℂ)
      exact this.const_mul (m z)
    · simp_rw [hnorm]
      exact hm.norm.div_const 2
  have hsw2 := integral_integral_swap (f := fun (s : ℝ) z => m z * (β (-(s + l' z) - s) : ℂ)) hprod2
  rw [hsw2]
  have hin : ∀ z, ∫ s : ℝ, m z * (β (-(s + l' z) - s) : ℂ) = m z / 2 := by
    intro z
    rw [integral_const_mul, integral_complex_ofReal, (flip_half β hi h1 (l' z)).2]
    push_cast
    ring
  simp_rw [hin]
  exact integral_div 2 m

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.flip_pf :
    Flip := by
  intro X Z _ _ ν _ μ _ l l' F m d hl hl' hF hFc hm hd hb hh
  have hmeas : Measurable (fun x => F (l x) x) := hF.comp (hl.prodMk measurable_id)
  refine ⟨hd.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun x => hb (l x) x (by simp)), ?_⟩
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun k =>
    ⟨1 / (2 * ((k : ℝ) + 1)), 1 / ((k : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      exact one_div_lt_one_div_of_lt this (by linarith)⟩
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let β : ℕ → ℝ → ℝ := fun k => (φ k).normed volume
  have hr : ∀ k t, β k t ≠ 0 → |t| ≤ 1 := by
    intro k t ht
    have hmem : t ∈ Function.support ((φ k).normed volume) := ht
    rw [(φ k).support_normed_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
    have : (φ k).rOut ≤ 1 := by
      show 1 / ((k : ℝ) + 1) ≤ 1
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := by positivity
      linarith
    linarith
  have hcore := fun k => flip_core ν μ l l' F m d hl hl' hF hm hd hb hh (β k)
    (φ k).continuous_normed (φ k).hasCompactSupport_normed (fun t => (φ k).nonneg_normed t)
    (φ k).integral_normed (hr k)
  have hlim : Tendsto (fun k => ∫ x, (∫ s : ℝ, F s x * (β k (l x - s) : ℂ)) ∂ν) atTop
      (𝓝 (∫ x, F (l x) x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence d (fun k => (hcore k).1.aestronglyMeasurable) hd
      (fun k => Eventually.of_forall (hcore k).2.1) (Eventually.of_forall fun x => ?_)
    have := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure ℝ))
      (g := fun s => F s x) hφ (hFc x) (l x)
    refine this.congr fun k => ?_
    rw [convolution_eq_swap]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp [β, mul_comm]
  have hconst : Tendsto (fun k => ∫ x, (∫ s : ℝ, F s x * (β k (l x - s) : ℂ)) ∂ν) atTop
      (𝓝 ((∫ z, m z ∂μ) / 2)) := by
    simp_rw [fun k => (hcore k).2.2]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hconst
