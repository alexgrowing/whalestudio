import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (hessC)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh locDens mInt MIntegrable)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem hessC_add_const_fun (f : (Fin D → ℂ) → ℝ) (c : ℝ) (z : Fin D → ℂ) :
    hessC (fun y => f y + c) z = hessC f z := by
  have h : fderiv ℝ (fun y => f y + c) = fderiv ℝ f := funext fun _ => fderiv_add_const c
  unfold hessC
  rw [h]

theorem locDens_potForm_congr (A : FinHolAtlas D X) (th : LocPot X) (u v : Fin D → X → ℝ)
    (W : Set X) (hW : IsOpen W) (j : Fin A.n) {y : Fin D → ℂ} (hy : y ∈ (A.chart j).target)
    (hyW : (A.chart j).symm y ∈ W) (hc : ∀ i, ∃ c : ℝ, ∀ x ∈ W, v i x = u i x + c) :
    locDens A (fun i => potForm th (v i)) j y = locDens A (fun i => potForm th (u i)) j y := by
  unfold ReciprocityTheory.AnForm.M.locDens
  refine ReciprocityTheory.AnForm.M.maDens_congr_hessC _ _ _ fun i => ?_
  obtain ⟨c, hc⟩ := hc i
  have hev : (fun y' => (potForm th (v i)).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => (potForm th (u i)).φ ((A.chart j).symm y) ((A.chart j).symm y') + c := by
    filter_upwards [((A.chart j).isOpen_inter_preimage_symm hW).mem_nhds ⟨hy, hyW⟩] with y' hy'
    show th.φ _ _ + v i _ = th.φ _ _ + u i _ + c
    rw [hc _ hy'.2]
    ring
  exact (ReciprocityTheory.AnForm.M.hessCGerm _ _ _ hev).trans (hessC_add_const_fun _ c y)

theorem measurableSet_chart_of_isOpen (A : FinHolAtlas D X) {S : Set X} (hS : IsOpen S) (j : Fin A.n) :
    MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) :=
  ((A.chart j).isOpen_inter_preimage_symm hS).measurableSet

theorem measurableSet_chart_diff (A : FinHolAtlas D X) {S S' : Set X} (j : Fin A.n)
    (hS : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S))
    (hS' : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S')) :
    MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (S \ S')) := by
  have h : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (S \ S') =
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) \
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S') := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff]
    tauto
  rw [h]
  exact hS.diff hS'

theorem measurableSet_chart_compl (A : FinHolAtlas D X) {S : Set X} (j : Fin A.n)
    (hS : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S)) :
    MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ) := by
  have h : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ =
      (A.chart j).target \ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_sdiff]
    tauto
  rw [h]
  exact (A.chart j).open_target.measurableSet.diff hS

theorem mIntegrable_indicator (A : FinHolAtlas D X) (Ψ : Fin D → LocPot X)
    (hΨ : ∀ i, IsPotential A (Ψ i)) (S : Set X)
    (hS : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S)) :
    MIntegrable A Ψ (S.indicator 1) := by
  intro j K hKt hK
  have h1 : IntegrableOn (locDens A Ψ j) K :=
    ((ReciprocityTheory.AnForm.M.locDensCont A Ψ hΨ j).mono hKt).integrableOn_compact hK
  refine (h1.indicator (hS j)).congr_fun (fun y hy => ?_) hK.measurableSet
  by_cases h : (A.chart j).symm y ∈ S
  · simp [h, hKt hy]
  · simp [h]

theorem mInt_indicator_union [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Ψ : Fin D → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (S S' : Set X)
    (hS : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S))
    (hS' : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S'))
    (hd : Disjoint S S') :
    mInt A Ψ ((S ∪ S').indicator 1) = mInt A Ψ (S.indicator 1) + mInt A Ψ (S'.indicator 1) := by
  have h := ReciprocityTheory.AnForm.M.mIntLinear A Ψ hΨ 1 _ _ (mIntegrable_indicator A Ψ hΨ S hS)
    (mIntegrable_indicator A Ψ hΨ S' hS')
  rw [one_mul] at h
  rw [← h]
  congr 1
  funext x
  rw [Set.indicator_union_of_disjoint hd, one_mul]

theorem mInt_one_split [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Ψ : Fin D → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (S : Set X)
    (hS : ∀ j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S)) :
    mInt A Ψ (fun _ => 1) = mInt A Ψ (S.indicator 1) + mInt A Ψ (Sᶜ.indicator 1) := by
  have h := mInt_indicator_union A Ψ hΨ S Sᶜ hS (fun j => measurableSet_chart_compl A j (hS j))
    disjoint_compl_right
  rw [Set.union_compl_self, Set.indicator_univ] at h
  exact h

theorem setIntegral_locDens_le_mInt [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Ψ : Fin D → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (hpsh : ∀ i, IsPsh A (Ψ i))
    (j : Fin A.n) (K : Set (Fin D → ℂ)) (hKt : K ⊆ (A.chart j).target) (hK : IsCompact K) :
    ∫ y in K, locDens A Ψ j y ≤ mInt A Ψ (fun _ => 1) := by
  have hKc : IsCompact ((A.chart j).symm '' K) :=
    hK.image_of_continuousOn ((A.chart j).continuousOn_symm.mono hKt)
  have hKs : (A.chart j).symm '' K ⊆ (A.chart j).source := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.chart j).map_target (hKt hy)
  obtain ⟨U, hU, hKU, hUs⟩ := normal_exists_closure_subset hKc.isClosed (A.chart j).open_source hKs
  obtain ⟨f, hf1, hf0, -, hf01⟩ := exists_continuous_one_zero_of_isCompact hKc hU.isClosed_compl
    (disjoint_compl_right.mono_left hKU)
  have hts : tsupport f ⊆ (A.chart j).source := by
    refine (closure_mono fun x hx => ?_).trans hUs
    by_contra h
    exact hx (hf0 h)
  have hint : MIntegrable A Ψ f := ReciprocityTheory.AnForm.M.mIntegrableCont A Ψ hΨ f f.continuous
  have hint' : MIntegrable A Ψ (fun x => 1 - f x) :=
    ReciprocityTheory.AnForm.M.mIntegrableCont A Ψ hΨ _ (continuous_const.sub f.continuous)
  have hne := ReciprocityTheory.AnForm.M.existsPartition A
  have hloc : mInt A Ψ f = ∫ y in (A.chart j).target, f ((A.chart j).symm y) * locDens A Ψ j y := by
    rw [ReciprocityTheory.AnForm.M.mIntEq A hne.some Ψ hΨ f hint]
    exact ReciprocityTheory.AnForm.M.mIntLocalize A hne.some Ψ hΨ j f hts hint
  have hT : IntegrableOn (fun y => f ((A.chart j).symm y) * locDens A Ψ j y) (A.chart j).target := by
    obtain ⟨hc, hsub⟩ := ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j) (isClosed_tsupport f) hts
    refine ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j) (Z := tsupport f)
      (fun y _ hy => ?_) (hint j _ hsub hc)
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have h1 : ∫ y in K, locDens A Ψ j y ≤ mInt A Ψ f := by
    rw [hloc]
    calc ∫ y in K, locDens A Ψ j y
        = ∫ y in K, f ((A.chart j).symm y) * locDens A Ψ j y := by
          refine setIntegral_congr_fun hK.measurableSet fun y hy => ?_
          simp [hf1 ⟨y, hy, rfl⟩]
      _ ≤ _ := by
          refine setIntegral_mono_set hT ?_ hKt.eventuallyLE
          filter_upwards [ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy
          exact mul_nonneg (hf01 _).1
            (ReciprocityTheory.AnForm.M.locDens_nonneg_of_psh A Ψ hΨ hpsh j hy)
  have h2 := ReciprocityTheory.AnForm.M.mIntLinear A Ψ hΨ 1 _ _ hint hint'
  have h3 : (fun x => 1 * f x + (1 - f x)) = fun _ : X => (1 : ℝ) := funext fun x => by ring
  rw [h3] at h2
  have h4 := ReciprocityTheory.AnForm.M.mIntNonneg A Ψ hΨ hpsh (fun x => 1 - f x)
    fun x => sub_nonneg.2 (hf01 x).2
  linarith

theorem integrable_of_tendsto_of_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : ℕ → α → ℝ} {F : α → ℝ} (hG : ∀ n, Integrable (G n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ G n x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 (F x))) (C : ℝ)
    (hC : ∀ n, ∫ x, G n x ∂μ ≤ C) : Integrable F μ := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hG n).1) hlim, ?_⟩
  have hF : ∫⁻ x, ‖F x‖ₑ ∂μ ≤ liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop :=
    lintegral_congr_ae (by filter_upwards [hlim] with x hx using hx.enorm.liminf_eq) ▸
      lintegral_liminf_le' (fun n => (hG n).1.aemeasurable.enorm)
  have hb : ∀ n, ∫⁻ x, ‖G n x‖ₑ ∂μ ≤ ENNReal.ofReal C := by
    intro n
    have h1 : ∫⁻ x, ‖G n x‖ₑ ∂μ = ENNReal.ofReal (∫ x, G n x ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hG n) (h0 n)]
      refine lintegral_congr_ae ?_
      filter_upwards [h0 n] with x hx
      exact Real.enorm_eq_ofReal hx
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hC n)
  exact (hF.trans (liminf_le_of_frequently_le' (Frequently.of_forall hb))).trans_lt
    ENNReal.ofReal_lt_top

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
