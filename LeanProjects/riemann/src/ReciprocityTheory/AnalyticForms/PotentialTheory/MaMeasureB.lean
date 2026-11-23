import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureA
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal

noncomputable section

def chartMeasure {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X) (j : Fin A.n) :
    Measure X :=
  ((volume.restrict (A.chart j).target).withDensity fun y =>
    ENNReal.ofReal (P.χ j ((A.chart j).symm y) * locDens A Φ j y)).map (A.chart j).symm

theorem maMeasure_eq_sum {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hne : Nonempty (ChartPartition A)) :
    maMeasure A Φ = ∑ j, chartMeasure A hne.some Φ j := by
  unfold maMeasure
  rw [dif_pos hne]
  rfl

theorem mInt_eq_integralWith {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hne : Nonempty (ChartPartition A))
    (g : X → ℝ) : mInt A Φ g = integralWith A hne.some Φ g := by
  unfold mInt
  rw [dif_pos hne]

theorem map_withDensity_integrable_integral {e : ℕ} {X : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {T : Set (Fin e → ℂ)} (hT : IsOpen T)
    {s : (Fin e → ℂ) → X} (hs : ContinuousOn s T) {w : (Fin e → ℂ) → ℝ} (hw : ContinuousOn w T)
    (hw0 : ∀ y ∈ T, 0 ≤ w y) {g : X → ℝ} (hg : Measurable g) :
    (Integrable g (((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s) ↔
      IntegrableOn (fun y => g (s y) * w y) T) ∧
    ∫ x, g x ∂(((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)).map s) =
      ∫ y in T, g (s y) * w y := by
  have hTm : MeasurableSet T := hT.measurableSet
  have hsm : AEMeasurable s (volume.restrict T) := hs.aemeasurable hTm
  have hwm : AEMeasurable (fun y => (w y).toNNReal) (volume.restrict T) :=
    (hw.aemeasurable hTm).real_toNNReal
  have hν : ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)) =
      (volume.restrict T).withDensity fun y => ((w y).toNNReal : ℝ≥0∞) := rfl
  have hsm' : AEMeasurable s ((volume.restrict T).withDensity fun y => ENNReal.ofReal (w y)) :=
    hsm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hae : (fun y => (w y).toNNReal • g (s y)) =ᵐ[volume.restrict T] (fun y => g (s y) * w y) := by
    filter_upwards [ae_restrict_mem hTm] with y hy
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hw0 y hy), smul_eq_mul, mul_comm]
  constructor
  · rw [integrable_map_measure hg.aestronglyMeasurable hsm', hν]
    exact (integrable_withDensity_iff_integrable_smul₀ hwm).trans (integrable_congr hae)
  · rw [integral_map hsm' hg.aestronglyMeasurable, hν, integral_withDensity_eq_integral_smul₀ hwm]
    exact integral_congr_ae hae

theorem integrableOn_target_of_closed {e : ℕ} {X : Type} [TopologicalSpace X]
    (ch : OpenPartialHomeomorph X (Fin e → ℂ)) {Z : Set X} {G : (Fin e → ℂ) → ℝ}
    (hG0 : ∀ y ∈ ch.target, ch.symm y ∉ Z → G y = 0) (hG : IntegrableOn G (ch '' Z)) :
    IntegrableOn G ch.target :=
  hG.of_forall_diff_eq_zero ch.open_target.measurableSet
    (fun y hy => hG0 y hy.1 (fun hz => hy.2 ⟨_, hz, ch.right_inv hy.1⟩))

theorem image_closed_compact {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (ch : OpenPartialHomeomorph X (Fin e → ℂ)) {Z : Set X} (hZ : IsClosed Z)
    (hZs : Z ⊆ ch.source) : IsCompact (ch '' Z) ∧ ch '' Z ⊆ ch.target :=
  ⟨hZ.isCompact.image_of_continuousOn (ch.continuousOn.mono hZs), by
    rintro _ ⟨x, hx, rfl⟩
    exact ch.map_source (hZs hx)⟩

theorem chi_comp_continuousOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    (P : ChartPartition A) (j : Fin A.n) :
    ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
  exact (P.smooth j j).continuousOn.mono (fun y hy => ⟨hy, Set.mem_univ _⟩)

theorem chi_le_one {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    (P : ChartPartition A) (j : Fin A.n) (x : X) : P.χ j x ≤ 1 := by
  exact (Finset.single_le_sum (f := fun i => P.χ i x) (fun i _ => P.nonneg i x)
    (Finset.mem_univ j)).trans (P.sum_eq_one x).le

theorem maMeasure_mono_of_psh {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Φ Θ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hΦp : ∀ i, IsPsh A (Φ i))
    (hΘ : ∀ i, IsPotential A (Θ i)) (hΘp : ∀ i, IsPsh A (Θ i)) :
    maMeasure A Φ ≤ maMeasure A (fun i => Φ i + Θ i) := by
  unfold maMeasure
  split_ifs with h
  · rw [Measure.le_iff]
    intro s hs
    simp only [Measure.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_le_sum fun j _ => ?_
    have hT := (A.chart j).open_target.measurableSet
    have hsm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
      (A.chart j).continuousOn_symm.aemeasurable hT
    have hle : (volume.restrict (A.chart j).target).withDensity (fun y =>
          ENNReal.ofReal (h.some.χ j ((A.chart j).symm y) * locDens A Φ j y)) ≤
        (volume.restrict (A.chart j).target).withDensity (fun y =>
          ENNReal.ofReal (h.some.χ j ((A.chart j).symm y) * locDens A (fun i => Φ i + Θ i) j y)) := by
      refine withDensity_mono ?_
      filter_upwards [ae_restrict_mem hT] with y hy
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (locDens_le_add A Φ Θ hΦ hΦp hΘ hΘp j hy) (h.some.nonneg j _))
    rw [Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _)) hs,
      Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _)) hs]
    exact Measure.le_iff'.1 hle _
  · exact le_rfl

variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]

theorem chartMeasure_integrable_integral (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i))
    (j : Fin A.n) {g : X → ℝ} (hg : Measurable g) (hgi : MIntegrable A Φ g) :
    Integrable g (chartMeasure A P Φ j) ∧
      ∫ x, g x ∂chartMeasure A P Φ j =
        ∫ y in (A.chart j).target, g ((A.chart j).symm y) *
          (P.χ j ((A.chart j).symm y) * locDens A Φ j y) := by
  have hT := (A.chart j).open_target
  have hw0 : ∀ y ∈ (A.chart j).target, 0 ≤ P.χ j ((A.chart j).symm y) * locDens A Φ j y :=
    fun y hy => mul_nonneg (P.nonneg j _) (locDens_nonneg_of_psh A Φ hΦ hPsh j hy)
  have hw : ContinuousOn (fun y => P.χ j ((A.chart j).symm y) * locDens A Φ j y)
      (A.chart j).target :=
    (chi_comp_continuousOn P j).mul (locDensCont A Φ hΦ j)
  obtain ⟨h1, h2⟩ := map_withDensity_integrable_integral hT (A.chart j).continuousOn_symm hw hw0 hg
  unfold chartMeasure
  refine ⟨h1.2 ?_, h2⟩
  obtain ⟨hK, hKs⟩ := image_closed_compact (A.chart j) (isClosed_tsupport (P.χ j))
    (P.tsupport_subset j)
  refine integrableOn_target_of_closed (A.chart j) (Z := tsupport (P.χ j)) ?_ ?_
  · intro y _ hz
    have h0 : P.χ j ((A.chart j).symm y) = 0 := by
      first
        | exact image_eq_zero_of_notMem_tsupport hz
        | exact image_eq_zero_of_nmem_tsupport hz
    rw [h0]
    ring
  · have hgK := hgi j _ hKs hK
    have hc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y))
        (A.chart j '' tsupport (P.χ j)) := (chi_comp_continuousOn P j).mono hKs
    have hm : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) *
        (g ((A.chart j).symm y) * locDens A Φ j y)) (A.chart j '' tsupport (P.χ j)) := by
      first
        | exact hgK.continuousOn_mul hc hK
        | exact IntegrableOn.continuousOn_mul hc hgK hK
        | exact hgK.continuousOn_mul hc hK.measurableSet
    refine hm.congr_fun (fun y _ => by ring) hK.measurableSet

theorem chartMeasure_finite (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i))
    (j : Fin A.n) : IsFiniteMeasure (chartMeasure A P Φ j) := by
  have hgi : MIntegrable A Φ (fun _ => (1 : ℝ)) := fun k K hKs hK => by
    have := ((locDensCont A Φ hΦ k).mono hKs).integrableOn_compact (μ := volume) hK
    simpa using this
  have hi := (chartMeasure_integrable_integral A P Φ hΦ hPsh j (g := fun _ => (1 : ℝ))
    measurable_const hgi).1
  first
    | exact (integrable_const_iff.1 hi).resolve_left one_ne_zero
    | exact ⟨(integrable_const_iff.1 hi).resolve_left one_ne_zero⟩

theorem maMeasure_forward (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i)) {g : X → ℝ} (hg : Measurable g)
    (hgi : MIntegrable A Φ g) :
    Integrable g (maMeasure A Φ) ∧ mInt A Φ g = ∫ x, g x ∂maMeasure A Φ := by
  by_cases hne : Nonempty (ChartPartition A)
  · rw [maMeasure_eq_sum A Φ hne, mInt_eq_integralWith A Φ hne]
    have hc := fun j => chartMeasure_integrable_integral A hne.some Φ hΦ hPsh j hg hgi
    refine ⟨integrable_finset_sum_measure.2 fun j _ => (hc j).1, ?_⟩
    rw [integral_finset_sum_measure fun j _ => (hc j).1]
    unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hc j).2]
    congr 1
    ext y
    ring
  · have h0 : maMeasure A Φ = 0 := by
      unfold maMeasure
      rw [dif_neg hne]
    have h0' : mInt A Φ g = 0 := by
      unfold mInt
      rw [dif_neg hne]
    rw [h0, h0']
    simp

private theorem absDet_clm_fin {e : ℕ} (f : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    |(f.restrictScalars ℝ).det| = ‖LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  have h : (f.restrictScalars ℝ).det =
      Algebra.norm ℝ (LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) := by
    first
      | exact LinearMap.det_restrictScalars
      | exact LinearMap.det_restrictScalars (f := (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))
  rw [h, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  exact abs_of_nonneg (by positivity)

theorem maMeasure_converse (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i)) {g : X → ℝ} (hg : Measurable g)
    (hgi : Integrable g (maMeasure A Φ)) : MIntegrable A Φ g := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hle : ∀ k, chartMeasure A hne.some Φ k ≤ maMeasure A Φ := by
    intro k
    rw [maMeasure_eq_sum A Φ hne, Measure.le_iff']
    intro s
    simp only [Measure.coe_finset_sum, Finset.sum_apply]
    exact Finset.single_le_sum (f := fun i => chartMeasure A hne.some Φ i s)
      (fun _ _ => by simp) (Finset.mem_univ k)
  have hF : ∀ k, IntegrableOn (fun z => g ((A.chart k).symm z) *
      (hne.some.χ k ((A.chart k).symm z) * locDens A Φ k z)) (A.chart k).target := by
    intro k
    have hw0 : ∀ y ∈ (A.chart k).target,
        0 ≤ hne.some.χ k ((A.chart k).symm y) * locDens A Φ k y :=
      fun y hy => mul_nonneg (hne.some.nonneg k _) (locDens_nonneg_of_psh A Φ hΦ hPsh k hy)
    have hw : ContinuousOn (fun y => hne.some.χ k ((A.chart k).symm y) * locDens A Φ k y)
        (A.chart k).target :=
      (chi_comp_continuousOn hne.some k).mul (locDensCont A Φ hΦ k)
    have h1 := (map_withDensity_integrable_integral (A.chart k).open_target
      (A.chart k).continuousOn_symm hw hw0 hg).1
    exact h1.1 (hgi.mono_measure (hle k))
  intro j K hKs hK
  have hKm : MeasurableSet K := hK.measurableSet
  have hterm : ∀ k, IntegrableOn (fun y => hne.some.χ k ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) K := by
    intro k
    have hUo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
      (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
    have hSm : MeasurableSet (K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source)) :=
      hKm.inter hUo.measurableSet
    have hder : ∀ y ∈ K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source),
        HasFDerivWithinAt (A.chart k ∘ (A.chart j).symm)
          ((fderiv ℂ (A.chart k ∘ (A.chart j).symm) y).restrictScalars ℝ)
          (K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source)) y := by
      intro y hy
      exact (((A.holo j k y hy.2).differentiableAt.hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
    have hinj : Set.InjOn (A.chart k ∘ (A.chart j).symm)
        (K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source)) := by
      intro y hy y' hy' h
      have h1 : (A.chart j).symm y = (A.chart j).symm y' :=
        (A.chart k).injOn hy.2.2 hy'.2.2 h
      exact (A.chart j).symm.injOn hy.2.1 hy'.2.1 h1
    have hcv := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume) hSm hder hinj
      (fun z => g ((A.chart k).symm z) *
        (hne.some.χ k ((A.chart k).symm z) * locDens A Φ k z))).1
      ((hF k).mono_set (by
        rintro _ ⟨y, hy, rfl⟩
        exact (A.chart k).map_source hy.2.2))
    have hS' : IntegrableOn (fun y => hne.some.χ k ((A.chart j).symm y) *
        (g ((A.chart j).symm y) * locDens A Φ j y))
        (K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source)) := by
      refine hcv.congr_fun (fun y hy => ?_) hSm
      have hl : (A.chart k).symm (A.chart k ((A.chart j).symm y)) = (A.chart j).symm y :=
        (A.chart k).left_inv hy.2.2
      simp only [smul_eq_mul, Function.comp_apply]
      rw [hl, locDensChart A Φ hΦ j k y hy.2.1 hy.2.2, absDet_clm_fin]
      ring
    refine hS'.of_forall_diff_eq_zero hKm ?_
    intro y hy
    have hyt : y ∈ (A.chart j).target := hKs hy.1
    have hnot : (A.chart j).symm y ∉ (A.chart k).source := fun h => hy.2 ⟨hy.1, hyt, h⟩
    have h0 : hne.some.χ k ((A.chart j).symm y) = 0 := by
      first
        | exact image_eq_zero_of_notMem_tsupport (fun h => hnot (hne.some.tsupport_subset k h))
        | exact image_eq_zero_of_nmem_tsupport (fun h => hnot (hne.some.tsupport_subset k h))
    rw [h0, zero_mul]
  have hsum : IntegrableOn (fun y => ∑ k, hne.some.χ k ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) K :=
    integrable_finset_sum Finset.univ (fun k _ => hterm k)
  refine hsum.congr_fun (fun y _ => ?_) hKm
  simp only
  rw [← Finset.sum_mul, hne.some.sum_eq_one, one_mul]

end

end ReciprocityTheory.AnForm.M
