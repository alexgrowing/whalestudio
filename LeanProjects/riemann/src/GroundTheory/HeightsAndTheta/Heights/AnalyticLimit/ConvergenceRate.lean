import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable ChartPartition integralWith
  locDens chartPartMeasure integral_chartPartMeasure isFiniteMeasure_chartPartMeasure existsPartition
  locDensCont mIntegrableCont)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def convRate (D : ℕ) (C t : ℝ) : ℝ :=
  C * (Real.log (ell t) / ell t + Real.log (ell t) ^ (D + 1) / ell t)

theorem tendsto_ell : Tendsto ell (𝓝[>] 0) atTop :=
  Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

theorem tendsto_convRate (D : ℕ) (C : ℝ) : Tendsto (convRate D C) (𝓝[>] 0) (𝓝 0) := by
  have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_ell
  have h2 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 (D + 1) one_ne_zero).comp tendsto_ell
  have h := (h1.add h2).const_mul C
  show Tendsto (fun t => C * (Real.log (ell t) / ell t + Real.log (ell t) ^ (D + 1) / ell t)) _ _
  simpa [Function.comp_def] using h

def ConvergenceRate.Statement : Prop :=
  ∀ (D : ℕ) (F : ℝ → ℝ) (C ℓ₀ : ℝ),
    (∀ t t', 0 < t' → t' ≤ t → ℓ₀ ≤ ell t → |F t - F t'| ≤ convRate D C t) →
    ∃ L : ℝ, Tendsto F (𝓝[>] 0) (𝓝 L) ∧
      ∀ t, 0 < t → ℓ₀ ≤ ell t → |F t - L| ≤ convRate D C t

theorem ConvergenceRate.proof : ConvergenceRate.Statement := by
  intro D F C ℓ₀ hF
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ℓ₀ ≤ ell t := tendsto_ell.eventually_ge_atTop ℓ₀
  have hc : Cauchy (map F (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    have hr : ∀ᶠ t in 𝓝[>] (0 : ℝ), convRate D C t < ε :=
      (tendsto_convRate D C).eventually (gt_mem_nhds hε)
    obtain ⟨δ, hδ, hδs⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 (hev.and hr)
    refine ⟨F '' Ioo 0 δ, mem_map.2 (mem_of_superset (Ioo_mem_nhdsGT hδ)
      (subset_preimage_image _ _)), ?_⟩
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
    rw [Real.dist_eq]
    rcases le_total t' t with h | h
    · exact (hF t t' ht'.1 h (hδs ht).1).trans_lt (hδs ht).2
    · rw [abs_sub_comm]
      exact (hF t' t ht.1 h (hδs ht').1).trans_lt (hδs ht').2
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hc
  refine ⟨L, hL, fun t ht hℓ => ?_⟩
  have hlim : Tendsto (fun t' => |F t - F t'|) (𝓝[>] 0) (𝓝 |F t - L|) :=
    (continuous_abs.tendsto _).comp (tendsto_const_nhds.sub hL)
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT ht] with t' ht'
  exact hF t t' ht'.1 ht'.2.le hℓ

section Signed

variable {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

def tvMeasure (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) : Measure X :=
  ∑ j, (chartPartMeasure A (existsPartition A).some Φ 1 j +
    chartPartMeasure A (existsPartition A).some Φ (-1) j)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem chart_weight_continuousOn (A : FinHolAtlas D X) (P : ChartPartition A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) :
    ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target := by
  have h := (P.smooth j j).continuousOn
  rw [Set.preimage_univ, Set.inter_univ] at h
  exact continuousOn_const.mul (h.mul (locDensCont A Φ hΦ j))

omit [CompactSpace X] [T2Space X] in

theorem integrableOn_chart_of_part (A : FinHolAtlas D X) (P : ChartPartition A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ)
    (hg : Measurable g) (hi : Integrable g (chartPartMeasure A P Φ s j)) :
    IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) (A.chart j).target := by
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hwc := chart_weight_continuousOn A P Φ hΦ s j
  have hsymm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hT
  have hd : AEMeasurable (fun y => ENNReal.ofReal
      (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) (volume.restrict (A.chart j).target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hwc.aemeasurable hT)
  have hlt : ∀ᵐ y ∂(volume.restrict (A.chart j).target), ENNReal.ofReal
      (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hsymm' : AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hfun : (fun y => (ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) *
      locDens A Φ j y))).toReal • (g ∘ (A.chart j).symm) y) = fun y => g ((A.chart j).symm y) *
        max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0 := by
    funext y
    rw [ENNReal.toReal_ofReal', smul_eq_mul, Function.comp_apply, mul_comm]
  unfold chartPartMeasure at hi
  rw [integrable_map_measure hg.aestronglyMeasurable hsymm',
    integrable_withDensity_iff_integrable_smul₀' hd hlt, hfun] at hi
  exact hi

theorem isFiniteMeasure_tvMeasure (A : FinHolAtlas D X) (Φ : Fin D → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) : IsFiniteMeasure (tvMeasure A Φ) := by
  refine ⟨?_⟩
  rw [tvMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  refine ENNReal.sum_lt_top.2 fun j _ => ?_
  have := isFiniteMeasure_chartPartMeasure A (existsPartition A).some Φ hΦ 1 j
  have := isFiniteMeasure_chartPartMeasure A (existsPartition A).some Φ hΦ (-1) j
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩

theorem abs_mInt_le (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (f : X → ℝ) (hf : Measurable f) (hfi : MIntegrable A Φ f) :
    Integrable f (tvMeasure A Φ) ∧ |mInt A Φ f| ≤ ∫ x, |f x| ∂tvMeasure A Φ := by
  have h1 := fun j => integral_chartPartMeasure A (existsPartition A).some Φ hΦ 1 j f hf hfi
  have h2 := fun j => integral_chartPartMeasure A (existsPartition A).some Φ hΦ (-1) j f hf hfi
  have hI : ∀ j, Integrable f (chartPartMeasure A (existsPartition A).some Φ 1 j +
      chartPartMeasure A (existsPartition A).some Φ (-1) j) :=
    fun j => (h1 j).1.add_measure (h2 j).1
  have hm : mInt A Φ f = ∑ j, (∫ x, f x ∂chartPartMeasure A (existsPartition A).some Φ 1 j -
      ∫ x, f x ∂chartPartMeasure A (existsPartition A).some Φ (-1) j) := by
    rw [mInt, dif_pos (existsPartition A)]
    unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(h1 j).2, (h2 j).2, ← integral_sub
      (integrableOn_chart_of_part A _ Φ hΦ 1 j f hf (h1 j).1)
      (integrableOn_chart_of_part A _ Φ hΦ (-1) j f hf (h2 j).1)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    rw [one_mul, neg_one_mul, ← mul_sub, max_zero_sub_max_neg_zero_eq_self]
    ring
  refine ⟨integrable_finsetSum_measure.2 fun j _ => hI j, ?_⟩
  rw [hm, tvMeasure, integral_finsetSum_measure fun j _ => (hI j).abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [integral_add_measure (h1 j).1.abs (h2 j).1.abs]
  exact (abs_sub _ _).trans (add_le_add abs_integral_le_integral_abs abs_integral_le_integral_abs)

structure TVBounds (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (Yo : Set X) (r : X → ℝ)
    (M CE : ℝ) : Prop where
  null : tvMeasure A Φ Yoᶜ = 0
  mass : (tvMeasure A Φ Yo).toReal ≤ M
  tailInt : ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ →
    Integrable ((tail Yo r R₀).indicator fun x => Real.log (r x)) (tvMeasure A Φ)
  tailLog : ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ →
    ∫ x, (tail Yo r R₀).indicator (fun x => Real.log (r x)) x ∂tvMeasure A Φ ≤
      CE * Real.log R₀ ^ (D + 1) / R₀

end Signed

def ConvergenceSigned.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (Φ : Fin D → LocPot X), (∀ i, IsPotential A (Φ i)) →
    ∀ (Yo : Set X) (r : X → ℝ) (M CE : ℝ), TVBounds A Φ Yo r M CE →
    ∀ f : X → ℝ, Measurable f → MIntegrable A Φ f →
    ∀ a K ℓ : ℝ, 0 ≤ a → 0 ≤ K → Real.exp 1 ≤ ℓ →
      (∀ x ∈ Yo, r x ≤ ℓ → |f x| ≤ a) → (∀ x ∈ Yo, ℓ < r x → |f x| ≤ K * Real.log (r x)) →
      |mInt A Φ f| ≤ a * M + K * (CE * Real.log ℓ ^ (D + 1) / ℓ)

theorem ConvergenceSigned.proof : ConvergenceSigned.Statement := by
  intro D X _ _ _ _ _ A Φ hΦ Yo r M CE hB f hf hfi a K ℓ ha hK hℓ hnear hfar
  have := isFiniteMeasure_tvMeasure A Φ hΦ
  obtain ⟨hfI, habs⟩ := abs_mInt_le A Φ hΦ f hf hfi
  set ind := (tail Yo r ℓ).indicator fun x => Real.log (r x) with hind
  have hindI : Integrable ind (tvMeasure A Φ) := hB.tailInt ℓ hℓ
  have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hind0 : ∀ x, 0 ≤ ind x := fun x => Set.indicator_nonneg
    (fun y hy => Real.log_nonneg (by linarith [hy.2])) x
  have hae : ∀ᵐ x ∂tvMeasure A Φ, x ∈ Yo := mem_ae_iff.2 hB.null
  have hpt : ∀ᵐ x ∂tvMeasure A Φ, |f x| ≤ a + K * ind x := by
    filter_upwards [hae] with x hx
    by_cases hr : r x ≤ ℓ
    · have := hnear x hx hr
      have := mul_nonneg hK (hind0 x)
      linarith
    · replace hr := not_le.1 hr
      have hxt : x ∈ tail Yo r ℓ := ⟨hx, hr.le⟩
      rw [hind, Set.indicator_of_mem hxt]
      have := hfar x hx hr
      linarith
  have hint : ∫ x, |f x| ∂tvMeasure A Φ ≤ ∫ x, (a + K * ind x) ∂tvMeasure A Φ :=
    integral_mono_ae hfI.abs ((integrable_const a).add (hindI.const_mul K)) hpt
  rw [integral_add (integrable_const a) (hindI.const_mul K), integral_const, integral_const_mul,
    smul_eq_mul] at hint
  have hmass : (tvMeasure A Φ).real univ ≤ M := by
    rw [Measure.real, ← measure_congr (ae_eq_univ.2 hB.null)]
    exact hB.mass
  have e1 : (tvMeasure A Φ).real univ * a ≤ M * a := mul_le_mul_of_nonneg_right hmass ha
  have e2 : K * ∫ x, ind x ∂tvMeasure A Φ ≤ K * (CE * Real.log ℓ ^ (D + 1) / ℓ) :=
    mul_le_mul_of_nonneg_left (hB.tailLog ℓ hℓ) hK
  linarith

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential)

@[instance_reducible] def projectiveLineBorel : MeasurableSpace (OnePoint ℂ) := borel _

attribute [local instance] projectiveLineBorel

theorem projectiveLine_borelSpace : BorelSpace (OnePoint ℂ) := ⟨rfl⟩

attribute [local instance] projectiveLine_borelSpace

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
