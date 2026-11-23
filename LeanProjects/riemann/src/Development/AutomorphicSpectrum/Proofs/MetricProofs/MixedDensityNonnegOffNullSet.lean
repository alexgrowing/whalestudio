import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensAddOfFunContinuousOn
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

namespace MeasOff

abbrev ov {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (j : Fin A.n) :
    Set (Fin e → ℂ) :=
  (A.chart j).target ∩ (A.chart j).symm ⁻¹' U

theorem isOpen_ov {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X}
    (hU : IsOpen U) (j : Fin A.n) : IsOpen (ov A U j) :=
  (A.chart j).isOpen_inter_preimage_symm hU

theorem locDens_chart_of_contDiffAt {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (j k : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hyk : (A.chart j).symm y ∈ (A.chart k).source)
    (hsm : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ ((A.chart j).symm y) ∘ (A.chart k).symm)
      (A.chart k ((A.chart j).symm y))) :
    locDens A Φ j y = locDens A Φ k (A.chart k ((A.chart j).symm y)) *
      Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart k ∘ (A.chart j).symm) y).det := by
  have hτ : AnalyticAt ℂ (A.chart k ∘ (A.chart j).symm) y := A.holo j k y ⟨hy, hyk⟩
  have hsk : (A.chart k).symm (A.chart k ((A.chart j).symm y)) = (A.chart j).symm y :=
    (A.chart k).left_inv hyk
  have hL : locDens A Φ k (A.chart k ((A.chart j).symm y)) =
      maDens (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y'))
        (A.chart k ((A.chart j).symm y)) := by
    simp only [locDens, hsk]
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp
    (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y'))
    (A.chart k ∘ (A.chart j).symm) y hτ hsm
  have key : locDens A Φ j y = maDens (fun i =>
      (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart k).symm y')) ∘
        (A.chart k ∘ (A.chart j).symm)) y := by
    unfold locDens
    apply maDens_congr_hessC
    intro i
    apply hessCGerm
    have hWo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
      (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
    filter_upwards [hWo.mem_nhds (show y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source
      from ⟨hy, hyk⟩)] with w hw
    simp only [Function.comp_apply]
    rw [(A.chart k).left_inv hw.2]
  rw [hL, key]
  exact hcomp

theorem sum_contDiffAt {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X}
    (hU : IsOpen U) {P Θ : LocPot X} {f : X → ℝ} (hP : IsPotential A P) (hΘ : IsPotential A Θ)
    (hf : A.SmoothOn U f) (x : X) (k : Fin A.n) {z : Fin e → ℂ} (hz : z ∈ ov A U k)
    (hzx : (A.chart k).symm z ∈ (P + LocPot.ofFun f + Θ).U x) :
    ContDiffAt ℝ 2 ((P + LocPot.ofFun f + Θ).φ x ∘ (A.chart k).symm) z := by
  have h1 := potSmoothAt A P hP x k ⟨hz.1, hzx.1.1⟩
  have h3 := potSmoothAt A Θ hΘ x k ⟨hz.1, hzx.2⟩
  have h2 : ContDiffAt ℝ 2 (f ∘ (A.chart k).symm) z :=
    ((hf k).contDiffAt ((isOpen_ov A hU k).mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)
  exact (h1.add h2).add h3

theorem measurable_indicator {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {U : Set X} (hU : IsOpen U) {g : X → ℝ} (hg : ContinuousOn g U) :
    Measurable (U.indicator g) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hg.measurable_piecewise continuousOn_const hU.measurableSet

section main

variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem restrict_target_eq (A : FinHolAtlas e X) {U : Set X}
    (hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) (j : Fin A.n) :
    (volume.restrict (A.chart j).target : Measure (Fin e → ℂ)) = volume.restrict (ov A U j) := by
  refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
  · refine measure_mono_null (fun y hy => ?_) (hnull j)
    exact ⟨hy.1, fun h => hy.2 ⟨hy.1, h⟩⟩
  · have : ov A U j \ (A.chart j).target = ∅ := by
      ext y; simp only [Set.mem_diff, Set.mem_empty_iff_false, iff_false]
      exact fun h => h.2 h.1.1
    rw [this, measure_empty]

theorem chi_continuousOn {A : FinHolAtlas e X} (P : ChartPartition A) (k j : Fin A.n) :
    ContinuousOn (fun y => P.χ k ((A.chart j).symm y)) (A.chart j).target :=
  (P.smooth k j).continuousOn.mono fun _ hy => ⟨hy, Set.mem_univ _⟩

theorem chart_integrable_integral (A : FinHolAtlas e X) (P : ChartPartition A) {U : Set X}
    (Φ : Fin e → LocPot X) (hU : IsOpen U)
    (hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0)
    (hcont : ∀ j, ContinuousOn (locDens A Φ j) (ov A U j))
    (hnn : ∀ j, ∀ y ∈ ov A U j, 0 ≤ locDens A Φ j y) (k : Fin A.n) {G : X → ℝ}
    (hG : Measurable G) :
    (Integrable G (chartMeasure A P Φ k) ↔ IntegrableOn (fun y => G ((A.chart k).symm y) *
      (P.χ k ((A.chart k).symm y) * locDens A Φ k y)) (ov A U k)) ∧
    ∫ x, G x ∂chartMeasure A P Φ k = ∫ y in ov A U k, G ((A.chart k).symm y) *
      (P.χ k ((A.chart k).symm y) * locDens A Φ k y) := by
  unfold chartMeasure
  rw [restrict_target_eq A hnull k]
  exact map_withDensity_integrable_integral (isOpen_ov A hU k)
    ((A.chart k).continuousOn_symm.mono Set.inter_subset_left)
    (((chi_continuousOn P k k).mono Set.inter_subset_left).mul (hcont k))
    (fun y hy => mul_nonneg (P.nonneg k _) (hnn k y hy)) hG

theorem chart_ae_mem (A : FinHolAtlas e X) (P : ChartPartition A) {U : Set X}
    (Φ : Fin e → LocPot X) (hU : IsOpen U)
    (hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) (k : Fin A.n) :
    ∀ᵐ x ∂chartMeasure A P Φ k, x ∈ U := by
  unfold chartMeasure
  rw [restrict_target_eq A hnull k]
  have hVm := (isOpen_ov A hU k).measurableSet
  have hsm : AEMeasurable (A.chart k).symm (volume.restrict (ov A U k)) :=
    ((A.chart k).continuousOn_symm.mono Set.inter_subset_left).aemeasurable hVm
  have hac := withDensity_absolutelyContinuous (volume.restrict (ov A U k)) (fun y =>
    ENNReal.ofReal (P.χ k ((A.chart k).symm y) * locDens A Φ k y))
  refine (ae_map_iff (hsm.mono_ac hac) (p := fun x => x ∈ U) hU.measurableSet).2 ?_
  exact hac.ae_le (ae_restrict_of_forall_mem hVm fun y hy => hy.2)

theorem lintegral_chart_le (A : FinHolAtlas e X) {U : Set X} (Φ : Fin e → LocPot X)
    (hU : IsOpen U) (hnn : ∀ j, ∀ y ∈ ov A U j, 0 ≤ locDens A Φ j y)
    (hch : ∀ j k, ∀ y ∈ ov A U j, (A.chart j).symm y ∈ (A.chart k).source →
      locDens A Φ j y = locDens A Φ k (A.chart k ((A.chart j).symm y)) *
        Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart k ∘ (A.chart j).symm) y).det)
    (j k : Fin A.n) (H : X → ENNReal) (hH : ∀ x, x ∉ (A.chart k).source → H x = 0) :
    ∫⁻ y in ov A U j, H ((A.chart j).symm y) * ENNReal.ofReal (locDens A Φ j y) ≤
      ∫⁻ z in ov A U k, H ((A.chart k).symm z) * ENNReal.ofReal (locDens A Φ k z) := by
  set W : Set (Fin e → ℂ) := ov A U k ∩ (A.chart k).symm ⁻¹' (A.chart j).source with hW
  set S : Set (Fin e → ℂ) := ov A U j ∩ (A.chart j).symm ⁻¹' (A.chart k).source with hS
  set τ : (Fin e → ℂ) → (Fin e → ℂ) := A.chart j ∘ (A.chart k).symm with hτd
  have hWo : IsOpen W := by
    have : W = (A.chart k).target ∩ (A.chart k).symm ⁻¹' (U ∩ (A.chart j).source) := by
      ext y
      simp only [hW, ov, Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [this]
    exact (A.chart k).isOpen_inter_preimage_symm (hU.inter (A.chart j).open_source)
  have hSo : IsOpen S := by
    have : S = (A.chart j).target ∩ (A.chart j).symm ⁻¹' (U ∩ (A.chart k).source) := by
      ext y
      simp only [hS, ov, Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [this]
    exact (A.chart j).isOpen_inter_preimage_symm (hU.inter (A.chart k).open_source)
  have hτ : AnalyticOnNhd ℂ τ W := (A.holo k j).mono fun z hz => ⟨hz.1.1, hz.2⟩
  have hinj : Set.InjOn τ W := fun a ha b hb hab =>
    (A.chart k).symm.injOn ha.1.1 hb.1.1 ((A.chart j).injOn ha.2 hb.2 hab)
  have himg : τ '' W = S := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hl : (A.chart j).symm (τ z) = (A.chart k).symm z := (A.chart j).left_inv hz.2
      refine ⟨⟨(A.chart j).map_source hz.2, ?_⟩, ?_⟩
      · show (A.chart j).symm (τ z) ∈ U
        rw [hl]; exact hz.1.2
      · show (A.chart j).symm (τ z) ∈ (A.chart k).source
        rw [hl]; exact (A.chart k).map_target hz.1.1
    · intro hy
      have hl : (A.chart k).symm (A.chart k ((A.chart j).symm y)) = (A.chart j).symm y :=
        (A.chart k).left_inv hy.2
      refine ⟨A.chart k ((A.chart j).symm y), ⟨⟨(A.chart k).map_source hy.2, ?_⟩, ?_⟩, ?_⟩
      · show (A.chart k).symm (A.chart k ((A.chart j).symm y)) ∈ U
        rw [hl]; exact hy.1.2
      · show (A.chart k).symm (A.chart k ((A.chart j).symm y)) ∈ (A.chart j).source
        rw [hl]; exact (A.chart j).map_target hy.1.1
      · show A.chart j ((A.chart k).symm (A.chart k ((A.chart j).symm y))) = y
        rw [hl]; exact (A.chart j).right_inv hy.1.1
  set F : (Fin e → ℂ) → ENNReal := fun y =>
    H ((A.chart j).symm y) * ENNReal.ofReal (locDens A Φ j y) with hF
  have h1 : ∫⁻ y in ov A U j, F y = ∫⁻ y in S, F y := by
    rw [← lintegral_indicator (isOpen_ov A hU j).measurableSet,
      ← lintegral_indicator hSo.measurableSet]
    refine lintegral_congr fun y => ?_
    by_cases hyS : y ∈ S
    · rw [Set.indicator_of_mem hyS, Set.indicator_of_mem hyS.1]
    · rw [Set.indicator_of_notMem hyS]
      by_cases hyV : y ∈ ov A U j
      · rw [Set.indicator_of_mem hyV]
        have : (A.chart j).symm y ∉ (A.chart k).source := fun h => hyS ⟨hyV, h⟩
        simp [hF, hH _ this]
      · rw [Set.indicator_of_notMem hyV]
  rw [h1, ← himg, ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ W hWo hτ hinj F]
  have h2 : ∫⁻ z in W, ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) * F (τ z) =
      ∫⁻ z in W, H ((A.chart k).symm z) * ENNReal.ofReal (locDens A Φ k z) := by
    refine setLIntegral_congr_fun hWo.measurableSet fun z hz => ?_
    have hl : (A.chart j).symm (τ z) = (A.chart k).symm z := (A.chart j).left_inv hz.2
    have hτS : τ z ∈ S := himg ▸ Set.mem_image_of_mem τ hz
    have hd := hch k j z hz.1 hz.2
    have hn := hnn j (τ z) hτS.1
    have hd' : locDens A Φ k z = locDens A Φ j (τ z) *
        Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det := hd
    simp only [hF, hl]
    rw [hd', ENNReal.ofReal_mul hn]
    ring
  rw [h2]
  exact lintegral_mono_set Set.inter_subset_left

theorem integrableOn_ov (A : FinHolAtlas e X) (P : ChartPartition A) {U : Set X}
    (Φ : Fin e → LocPot X) (hU : IsOpen U)
    (hcont : ∀ j, ContinuousOn (locDens A Φ j) (ov A U j))
    (hnn : ∀ j, ∀ y ∈ ov A U j, 0 ≤ locDens A Φ j y)
    (hch : ∀ j k, ∀ y ∈ ov A U j, (A.chart j).symm y ∈ (A.chart k).source →
      locDens A Φ j y = locDens A Φ k (A.chart k ((A.chart j).symm y)) *
        Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart k ∘ (A.chart j).symm) y).det)
    {G : X → ℝ} (hG : Measurable G)
    (hI : ∀ k, IntegrableOn (fun y => G ((A.chart k).symm y) *
      (P.χ k ((A.chart k).symm y) * locDens A Φ k y)) (ov A U k)) (j : Fin A.n) :
    IntegrableOn (fun y => G ((A.chart j).symm y) * locDens A Φ j y) (ov A U j) := by
  have hVm := (isOpen_ov A hU j).measurableSet
  have hsm : AEMeasurable (A.chart j).symm (volume.restrict (ov A U j)) :=
    ((A.chart j).continuousOn_symm.mono Set.inter_subset_left).aemeasurable hVm
  have hdm : AEMeasurable (locDens A Φ j) (volume.restrict (ov A U j)) :=
    (hcont j).aemeasurable hVm
  have hGm : AEMeasurable (fun y => G ((A.chart j).symm y)) (volume.restrict (ov A U j)) :=
    hG.comp_aemeasurable hsm
  refine ⟨(hGm.mul hdm).aestronglyMeasurable, ?_⟩
  set H : Fin A.n → X → ENNReal := fun k x => ‖G x‖ₑ * ENNReal.ofReal (P.χ k x) with hHd
  have hsum : ∀ x, ∑ k, ENNReal.ofReal (P.χ k x) = 1 := fun x => by
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => P.nonneg k x, P.sum_eq_one, ENNReal.ofReal_one]
  have hpt : ∫⁻ y in ov A U j, ‖G ((A.chart j).symm y) * locDens A Φ j y‖ₑ =
      ∫⁻ y in ov A U j, ∑ k, H k ((A.chart j).symm y) * ENNReal.ofReal (locDens A Φ j y) := by
    refine setLIntegral_congr_fun hVm fun y hy => ?_
    simp only [hHd]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one, enorm_mul,
      Real.enorm_of_nonneg (hnn j y hy)]
  have hHm : ∀ k, AEMeasurable (fun y => H k ((A.chart j).symm y) *
      ENNReal.ofReal (locDens A Φ j y)) (volume.restrict (ov A U j)) := fun k =>
    ((hGm.enorm).mul ((((chi_continuousOn P k j).mono Set.inter_subset_left).aemeasurable
      hVm).ennreal_ofReal)).mul hdm.ennreal_ofReal
  show ∫⁻ y in ov A U j, ‖G ((A.chart j).symm y) * locDens A Φ j y‖ₑ < ⊤
  rw [hpt, lintegral_finset_sum' _ fun k _ => hHm k]
  refine ENNReal.sum_lt_top.2 fun k _ => ?_
  refine (lintegral_chart_le A Φ hU hnn hch j k (H k) fun x hx => ?_).trans_lt ?_
  · have : x ∉ tsupport (P.χ k) := fun h => hx (P.tsupport_subset k h)
    simp [hHd, image_eq_zero_of_notMem_tsupport this]
  · have hk := (hI k).2
    have hcg : ∫⁻ z in ov A U k, H k ((A.chart k).symm z) * ENNReal.ofReal (locDens A Φ k z) =
        ∫⁻ z in ov A U k, ‖G ((A.chart k).symm z) *
          (P.χ k ((A.chart k).symm z) * locDens A Φ k z)‖ₑ := by
      refine setLIntegral_congr_fun (isOpen_ov A hU k).measurableSet fun z hz => ?_
      simp only [hHd]
      rw [enorm_mul, enorm_mul, Real.enorm_of_nonneg (hnn k z hz),
        Real.enorm_of_nonneg (P.nonneg k _), mul_assoc]
    rw [hcg]
    exact hk

variable [CompactSpace X] [T2Space X]

theorem mInt_eq_of_dens (A : FinHolAtlas e X) {U : Set X} (Φ : Fin e → LocPot X) (hU : IsOpen U)
    (hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0)
    (hcont : ∀ j, ContinuousOn (locDens A Φ j) (ov A U j))
    (hnn : ∀ j, ∀ y ∈ ov A U j, 0 ≤ locDens A Φ j y)
    (hch : ∀ j k, ∀ y ∈ ov A U j, (A.chart j).symm y ∈ (A.chart k).source →
      locDens A Φ j y = locDens A Φ k (A.chart k ((A.chart j).symm y)) *
        Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart k ∘ (A.chart j).symm) y).det)
    {g : X → ℝ} (hgc : ContinuousOn g U) (hgi : Integrable g (maMeasure A Φ)) :
    MIntegrable A Φ g ∧ mInt A Φ g = ∫ y, g y ∂maMeasure A Φ := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set P := hne.some with hPd
  have hG := measurable_indicator hU hgc
  rw [maMeasure_eq_sum A Φ hne] at hgi ⊢
  have hgk : ∀ k, Integrable g (chartMeasure A P Φ k) := fun k =>
    integrable_finsetSum_measure.mp hgi k (Finset.mem_univ k)
  have hae : ∀ k, U.indicator g =ᵐ[chartMeasure A P Φ k] g := fun k =>
    (chart_ae_mem A P Φ hU hnull k).mono fun x hx => Set.indicator_of_mem hx g
  have hfacts := fun k => chart_integrable_integral A P Φ hU hnull hcont hnn k hG
  have hI := fun k => (hfacts k).1.mp ((hgk k).congr (hae k).symm)
  refine ⟨fun j K hK hKc => ?_, ?_⟩
  · have h1 := integrableOn_ov A P Φ hU hcont hnn hch hG hI j
    have h2 : IntegrableOn (fun y => U.indicator g ((A.chart j).symm y) * locDens A Φ j y)
        (A.chart j).target := by
      unfold IntegrableOn
      rw [restrict_target_eq A hnull j]
      exact h1
    have hev : ∀ᵐ y ∂(volume.restrict (A.chart j).target),
        U.indicator g ((A.chart j).symm y) * locDens A Φ j y =
          g ((A.chart j).symm y) * locDens A Φ j y := by
      rw [restrict_target_eq A hnull j]
      refine ae_restrict_of_forall_mem (isOpen_ov A hU j).measurableSet fun y hy => ?_
      rw [Set.indicator_of_mem (show (A.chart j).symm y ∈ U from hy.2)]
    exact (h2.mono_set hK).congr (ae_restrict_of_ae_restrict_of_subset hK hev)
  · rw [mInt_eq_integralWith A Φ hne, integral_finsetSum_measure fun k _ => hgk k]
    unfold integralWith
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_congr_ae (hae k), (hfacts k).2, restrict_target_eq A hnull k]
    refine setIntegral_congr_fun (isOpen_ov A hU k).measurableSet fun y hy => ?_
    rw [Set.indicator_of_mem (show (A.chart k).symm y ∈ U from hy.2)]
    ring

end main

end MeasOff

theorem mInt_eq_integral_maMeasure_off_null : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) → (∀ i, IsPotential A (P i)) → IsPotential A Θ → IsPsh A Θ → (∀ i, A.SmoothOn U (f i)) → (∀ i, IsPshOn A U (P i + LocPot.ofFun (f i) + Θ)) → ∀ g : X → ℝ, ContinuousOn g U → Integrable g (maMeasure A fun i => P i + LocPot.ofFun (f i) + Θ) → MIntegrable A (fun i => P i + LocPot.ofFun (f i) + Θ) g ∧ mInt A (fun i => P i + LocPot.ofFun (f i) + Θ) g = ∫ y, g y ∂(maMeasure A fun i => P i + LocPot.ofFun (f i) + Θ) := by
  intro e X _ _ _ _ _ A U P f Θ hU hnull hP hΘ _ hf hpsh g hgc hgi
  refine MeasOff.mInt_eq_of_dens A _ hU hnull
    (fun j => locDens_add_ofFun_continuousOn A U P f Θ hU hP hΘ hf j) ?_ ?_ hgc hgi
  · intro j y hy
    refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y fun i => ?_
    exact hessC_posSemidef_of_levi _ y
      (MeasOff.sum_contDiffAt A hU (hP i) hΘ (hf i) _ j hy (LocPot.mem_U _ _))
      (fun w => hpsh i _ j y ⟨hy.1, LocPot.mem_U _ _, hy.2⟩ w)
  · intro j k y hy hyk
    refine MeasOff.locDens_chart_of_contDiffAt A _ j k hy.1 hyk fun i => ?_
    have hl : (A.chart k).symm (A.chart k ((A.chart j).symm y)) = (A.chart j).symm y :=
      (A.chart k).left_inv hyk
    refine MeasOff.sum_contDiffAt A hU (hP i) hΘ (hf i) _ k
      ⟨(A.chart k).map_source hyk, ?_⟩ ?_
    · show (A.chart k).symm (A.chart k ((A.chart j).symm y)) ∈ U
      rw [hl]; exact hy.2
    · rw [hl]; exact LocPot.mem_U _ _

end GlobalTheory.CompanionTheory.Ar.Giv
