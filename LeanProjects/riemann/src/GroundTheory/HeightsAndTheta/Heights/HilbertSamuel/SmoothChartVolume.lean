import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PChartPartitionExists
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithRes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ChartVolume

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def trans (A : FinHolAtlas e X) (j i : Fin A.n) : (Fin e → ℂ) → (Fin e → ℂ) :=
  A.chart i ∘ (A.chart j).symm

def overlap (A : FinHolAtlas e X) (j i : Fin A.n) : Set (Fin e → ℂ) :=
  (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source

theorem isOpen_overlap (A : FinHolAtlas e X) (j i : Fin A.n) : IsOpen (overlap A j i) :=
  (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
    (A.chart i).open_source

theorem analyticOnNhd_trans (A : FinHolAtlas e X) (j i : Fin A.n) :
    AnalyticOnNhd ℂ (trans A j i) (overlap A j i) :=
  A.holo j i

theorem image_trans (A : FinHolAtlas e X) (j i : Fin A.n) :
    trans A j i '' overlap A j i = overlap A i j := by
  ext w
  constructor
  · rintro ⟨y, ⟨hy, hyi⟩, rfl⟩
    refine ⟨(A.chart i).map_source hyi, ?_⟩
    show (A.chart i).symm (A.chart i ((A.chart j).symm y)) ∈ (A.chart j).source
    rw [(A.chart i).left_inv hyi]
    exact (A.chart j).map_target hy
  · rintro ⟨hw, hwj⟩
    refine ⟨A.chart j ((A.chart i).symm w), ⟨(A.chart j).map_source hwj, ?_⟩, ?_⟩
    · show (A.chart j).symm (A.chart j ((A.chart i).symm w)) ∈ (A.chart i).source
      rw [(A.chart j).left_inv hwj]
      exact (A.chart i).map_target hw
    · show A.chart i ((A.chart j).symm (A.chart j ((A.chart i).symm w))) = w
      rw [(A.chart j).left_inv hwj, (A.chart i).right_inv hw]

theorem injOn_trans (A : FinHolAtlas e X) (j i : Fin A.n) : InjOn (trans A j i) (overlap A j i) :=
  fun _ ha _ hb hab => (A.chart j).symm.injOn ha.1 hb.1 ((A.chart i).injOn ha.2 hb.2 hab)

theorem analyticOnNhd_det_jacC {τ : (Fin e → ℂ) → (Fin e → ℂ)} {U : Set (Fin e → ℂ)}
    (hτ : AnalyticOnNhd ℂ τ U) : AnalyticOnNhd ℂ (fun y => (jacC τ y).det) U := by
  intro y hy
  have he : ∀ a k, AnalyticAt ℂ (fun y => jacC τ y a k) y := by
    intro a k
    let L : ((Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj a).comp (ContinuousLinearMap.apply ℂ (Fin e → ℂ) (Pi.single k 1))
    have h : (fun y => jacC τ y a k) = L ∘ fderiv ℂ τ := by
      funext w
      simp [jacC, L]
    rw [h]
    exact (L.analyticAt _).comp (hτ.fderiv y hy)
  have h : (fun y => (jacC τ y).det) =
      fun y => ∑ σ : Equiv.Perm (Fin e), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, jacC τ y (σ i) i := by
    funext w
    rw [Matrix.det_apply]
    simp [Units.smul_def, zsmul_eq_mul]
  have h2 : (fun y => ∑ σ : Equiv.Perm (Fin e), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, jacC τ y (σ i) i) =
      ∑ σ : Equiv.Perm (Fin e), (fun _ => ((Equiv.Perm.sign σ : ℤ) : ℂ)) *
        ∏ i, fun y => jacC τ y (σ i) i := by
    funext w
    simp [Finset.sum_apply, Finset.prod_apply]
  rw [h, h2]
  exact Finset.analyticAt_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_prod _ fun i _ => he _ _)

def jac (A : FinHolAtlas e X) (j i : Fin A.n) (y : Fin e → ℂ) : ℝ :=
  Complex.normSq (jacC (trans A j i) y).det

theorem contDiffOn_jac (A : FinHolAtlas e X) (j i : Fin A.n) :
    ContDiffOn ℝ ∞ (jac A j i) (overlap A j i) := by
  have h1 : ContDiffOn ℂ ∞ (fun y => (jacC (trans A j i) y).det) (overlap A j i) :=
    (analyticOnNhd_det_jacC (analyticOnNhd_trans A j i)).contDiffOn
      (isOpen_overlap A j i).uniqueDiffOn
  have h2 := h1.restrict_scalars ℝ
  have h3 : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have h : jac A j i = (fun z : ℂ => ‖z‖ ^ 2) ∘ (fun y => (jacC (trans A j i) y).det) := by
    funext y
    simp [jac, Complex.normSq_eq_norm_sq]
  rw [h]
  exact h3.comp_contDiffOn h2

theorem det_jacC_trans_ne_zero (A : FinHolAtlas e X) (j i : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ overlap A j i) : (jacC (trans A j i) y).det ≠ 0 := by
  rw [det_jacC]
  have hyi : trans A j i y ∈ overlap A i j := image_trans A j i ▸ mem_image_of_mem _ hy
  have h1 : DifferentiableAt ℂ (trans A j i) y := (analyticOnNhd_trans A j i y hy).differentiableAt
  have h2 : DifferentiableAt ℂ (trans A i j) (trans A j i y) :=
    (analyticOnNhd_trans A i j _ hyi).differentiableAt
  have hid : trans A i j ∘ trans A j i =ᶠ[𝓝 y] id := by
    filter_upwards [(isOpen_overlap A j i).mem_nhds hy] with w hw
    show A.chart j ((A.chart i).symm (A.chart i ((A.chart j).symm w))) = w
    rw [(A.chart i).left_inv hw.2, (A.chart j).right_inv hw.1]
  have hc := fderiv_comp y h2 h1
  rw [hid.fderiv_eq, fderiv_id] at hc
  have hlin : ((fderiv ℂ (trans A i j) (trans A j i y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).comp
      (fderiv ℂ (trans A j i) y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    have hv := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L v) hc
    simpa using hv.symm
  have h := congrArg LinearMap.det hlin
  rw [LinearMap.det_comp, LinearMap.det_id] at h
  exact right_ne_zero_of_mul_eq_one h

def pieceDens (A : FinHolAtlas e X) (ψ : ChartPartition A) (j i : Fin A.n) (y : Fin e → ℂ) : ℝ :=
  (overlap A j i).indicator (fun y => ψ.χ i ((A.chart j).symm y) * jac A j i y) y

theorem pieceDens_nonneg (A : FinHolAtlas e X) (ψ : ChartPartition A) (j i : Fin A.n)
    (y : Fin e → ℂ) : 0 ≤ pieceDens A ψ j i y :=
  indicator_nonneg (fun _ _ => mul_nonneg (ψ.nonneg _ _) (Complex.normSq_nonneg _)) _

theorem contDiffOn_pieceDens (A : FinHolAtlas e X) (ψ : ChartPartition A) (j i : Fin A.n) :
    ContDiffOn ℝ ∞ (pieceDens A ψ j i) (A.chart j).target := by
  intro y hy
  refine ContDiffAt.contDiffWithinAt ?_
  have hψ : ContDiffOn ℝ ∞ (fun y => ψ.χ i ((A.chart j).symm y)) (A.chart j).target := by
    have h := ψ.smooth i j
    simpa [FinHolAtlas.Smooth, FinHolAtlas.SmoothOn, Function.comp_def] using h
  by_cases hyo : y ∈ overlap A j i
  · have hev : pieceDens A ψ j i =ᶠ[𝓝 y] fun y => ψ.χ i ((A.chart j).symm y) * jac A j i y := by
      filter_upwards [(isOpen_overlap A j i).mem_nhds hyo] with w hw
      simp [pieceDens, indicator_of_mem hw]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact ((hψ.mono inter_subset_left).mul (contDiffOn_jac A j i)).contDiffAt
      ((isOpen_overlap A j i).mem_nhds hyo)
  · have hns : (A.chart j).symm y ∉ tsupport (ψ.χ i) := fun h => hyo ⟨hy, ψ.tsupport_subset i h⟩
    have hW : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (tsupport (ψ.χ i))ᶜ) :=
      (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
        (isClosed_tsupport _).isOpen_compl
    have hev : pieceDens A ψ j i =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hW.mem_nhds ⟨hy, hns⟩] with w hw
      by_cases hwo : w ∈ overlap A j i
      · simp [pieceDens, indicator_of_mem hwo, image_eq_zero_of_notMem_tsupport hw.2]
      · simp [pieceDens, indicator_of_notMem hwo]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem pieceDens_pos (A : FinHolAtlas e X) (ψ : ChartPartition A) (j i : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hi : 0 < ψ.χ i ((A.chart j).symm y)) :
    0 < pieceDens A ψ j i y := by
  have hyo : y ∈ overlap A j i :=
    ⟨hy, ψ.tsupport_subset i (subset_tsupport _ (Function.mem_support.mpr hi.ne'))⟩
  rw [pieceDens, indicator_of_mem hyo]
  exact mul_pos hi (Complex.normSq_pos.mpr (det_jacC_trans_ne_zero A j i hyo))

def dens (A : FinHolAtlas e X) (ψ : ChartPartition A) (j : Fin A.n) (y : Fin e → ℂ) : ℝ :=
  ∑ i, pieceDens A ψ j i y

theorem contDiffOn_dens (A : FinHolAtlas e X) (ψ : ChartPartition A) (j : Fin A.n) :
    ContDiffOn ℝ ∞ (dens A ψ j) (A.chart j).target := by
  have h : dens A ψ j = fun y => ∑ i, pieceDens A ψ j i y := rfl
  rw [h]
  exact ContDiffOn.sum fun i _ => contDiffOn_pieceDens A ψ j i

theorem dens_pos (A : FinHolAtlas e X) (ψ : ChartPartition A) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) : 0 < dens A ψ j y := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < ψ.χ i ((A.chart j).symm y) := by
    by_contra h
    push Not at h
    have h1 := ψ.sum_eq_one ((A.chart j).symm y)
    have h2 : ∑ i, ψ.χ i ((A.chart j).symm y) ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  exact (pieceDens_pos A ψ j i hy hi).trans_le
    (Finset.single_le_sum (fun k _ => pieceDens_nonneg A ψ j k y) (Finset.mem_univ i))

variable [MeasurableSpace X] [BorelSpace X]

theorem measurableSet_chart_preimage (A : FinHolAtlas e X) (j : Fin A.n) {S : Set X}
    (hS : MeasurableSet S) : MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) := by
  have hc : Continuous ((A.chart j).target.restrict (A.chart j).symm) :=
    (A.chart j).continuousOn_symm.restrict
  have h := MeasurableSet.subtype_image (A.chart j).open_target.measurableSet (hc.measurable hS)
  convert h using 1
  ext y
  constructor
  · rintro ⟨hy, hyS⟩
    exact ⟨⟨y, hy⟩, hyS, rfl⟩
  · rintro ⟨⟨y, hy⟩, hyS, rfl⟩
    exact ⟨hy, hyS⟩

theorem lintegral_piece (A : FinHolAtlas e X) (ψ : ChartPartition A) (j i : Fin A.n) {S : Set X}
    (hS : MeasurableSet S) (hSj : S ⊆ (A.chart j).source) :
    ∫⁻ z in (A.chart i).target ∩ (A.chart i).symm ⁻¹' S, ENNReal.ofReal (ψ.χ i ((A.chart i).symm z)) =
      ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S, ENNReal.ofReal (pieceDens A ψ j i y) := by
  set B := (A.chart i).target ∩ (A.chart i).symm ⁻¹' S with hBdef
  set C := (A.chart j).target ∩ (A.chart j).symm ⁻¹' S with hCdef
  have hB : MeasurableSet B := measurableSet_chart_preimage A i hS
  have hC : MeasurableSet C := measurableSet_chart_preimage A j hS
  set G : (Fin e → ℂ) → ENNReal := B.indicator fun z => ENNReal.ofReal (ψ.χ i ((A.chart i).symm z))
    with hGdef
  set H : (Fin e → ℂ) → ENNReal := C.indicator fun y => ENNReal.ofReal (pieceDens A ψ j i y)
    with hHdef
  have hGs : Function.support G ⊆ overlap A i j := by
    intro z hz
    have hzB : z ∈ B := by
      by_contra h
      exact hz (indicator_of_notMem h _)
    exact ⟨hzB.1, hSj hzB.2⟩
  have hHs : Function.support H ⊆ overlap A j i := by
    intro y hy
    by_contra h
    apply hy
    by_cases hyC : y ∈ C
    · simp [H, indicator_of_mem hyC, pieceDens, indicator_of_notMem h]
    · exact indicator_of_notMem hyC _
  rw [← lintegral_indicator hB, ← lintegral_indicator hC, ← hGdef, ← hHdef,
    ← setLIntegral_eq_of_support_subset hGs, ← setLIntegral_eq_of_support_subset hHs,
    ← image_trans A j i, lintegral_image_eq_lintegral_normSq_det_mul _ _ (isOpen_overlap A j i)
      (analyticOnNhd_trans A j i) (injOn_trans A j i)]
  refine setLIntegral_congr_fun (isOpen_overlap A j i).measurableSet fun y hy => ?_
  have hsym : (A.chart i).symm (trans A j i y) = (A.chart j).symm y := (A.chart i).left_inv hy.2
  have htar : trans A j i y ∈ (A.chart i).target := (A.chart i).map_source hy.2
  by_cases hyS : (A.chart j).symm y ∈ S
  · have hB' : trans A j i y ∈ B := ⟨htar, by rw [Set.mem_preimage, hsym]; exact hyS⟩
    have hC' : y ∈ C := ⟨hy.1, hyS⟩
    simp only [G, H, indicator_of_mem hB', indicator_of_mem hC', hsym, pieceDens,
      indicator_of_mem hy, jac]
    rw [← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
    congr 1
    ring
  · have hB' : trans A j i y ∉ B := fun h => hyS (by
      have h2 := h.2
      rwa [Set.mem_preimage, hsym] at h2)
    have hC' : y ∉ C := fun h => hyS h.2
    simp [G, H, indicator_of_notMem hB', indicator_of_notMem hC']

def piece (A : FinHolAtlas e X) (ψ : ChartPartition A) (i : Fin A.n) : Measure X :=
  ((volume.restrict (A.chart i).target).withDensity
    fun z => ENNReal.ofReal (ψ.χ i ((A.chart i).symm z))).map (A.chart i).symm

theorem piece_apply (A : FinHolAtlas e X) (ψ : ChartPartition A) (i : Fin A.n) {S : Set X}
    (hS : MeasurableSet S) :
    piece A ψ i S = ∫⁻ z in (A.chart i).target ∩ (A.chart i).symm ⁻¹' S,
      ENNReal.ofReal (ψ.χ i ((A.chart i).symm z)) := by
  have hae : AEMeasurable (A.chart i).symm (volume.restrict (A.chart i).target) :=
    (A.chart i).continuousOn_symm.aemeasurable (A.chart i).open_target.measurableSet
  rw [piece, Measure.map_apply_of_aemeasurable (hae.mono_ac (withDensity_absolutelyContinuous _ _))
    hS, withDensity_apply', Measure.restrict_restrict' (A.chart i).open_target.measurableSet,
    inter_comm]

def vol (A : FinHolAtlas e X) (ψ : ChartPartition A) : Measure X :=
  ∑ i, piece A ψ i

theorem vol_apply_chart (A : FinHolAtlas e X) (ψ : ChartPartition A) (j : Fin A.n) {S : Set X}
    (hS : MeasurableSet S) (hSj : S ⊆ (A.chart j).source) :
    vol A ψ S = ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S,
      ENNReal.ofReal (dens A ψ j y) := by
  rw [vol, Measure.finsetSum_apply]
  simp_rw [piece_apply A ψ _ hS, lintegral_piece A ψ j _ hS hSj]
  rw [← lintegral_finsetSum']
  · refine setLIntegral_congr_fun (measurableSet_chart_preimage A j hS) fun y _ => ?_
    rw [dens, ENNReal.ofReal_sum_of_nonneg fun i _ => pieceDens_nonneg A ψ j i y]
  · intro i _
    exact (((contDiffOn_pieceDens A ψ j i).continuousOn.mono inter_subset_left).aemeasurable
      (measurableSet_chart_preimage A j hS)).ennreal_ofReal

theorem piece_univ_lt_top (A : FinHolAtlas e X) (ψ : ChartPartition A) [CompactSpace X]
    (i : Fin A.n) : piece A ψ i univ < ⊤ := by
  have hT : IsCompact (tsupport (ψ.χ i)) := (isClosed_tsupport _).isCompact
  have hK : IsCompact (A.chart i '' tsupport (ψ.χ i)) :=
    hT.image_of_continuousOn ((A.chart i).continuousOn.mono (ψ.tsupport_subset i))
  have hKm : MeasurableSet (A.chart i '' tsupport (ψ.χ i)) := hK.isClosed.measurableSet
  rw [piece_apply A ψ i MeasurableSet.univ, preimage_univ, inter_univ]
  calc ∫⁻ z in (A.chart i).target, ENNReal.ofReal (ψ.χ i ((A.chart i).symm z))
      ≤ ∫⁻ z in (A.chart i).target, (A.chart i '' tsupport (ψ.χ i)).indicator 1 z := by
        refine setLIntegral_mono (measurable_one.indicator hKm) fun z hz => ?_
        by_cases h0 : ψ.χ i ((A.chart i).symm z) = 0
        · simp [h0]
        · have hmem : z ∈ A.chart i '' tsupport (ψ.χ i) :=
            ⟨(A.chart i).symm z, subset_tsupport _ (Function.mem_support.mpr h0),
              (A.chart i).right_inv hz⟩
          rw [indicator_of_mem hmem, Pi.one_apply, ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← ψ.sum_eq_one ((A.chart i).symm z)]
          exact Finset.single_le_sum (fun k _ => ψ.nonneg k _) (Finset.mem_univ i)
    _ ≤ ∫⁻ z, (A.chart i '' tsupport (ψ.χ i)).indicator 1 z := setLIntegral_le_lintegral _ _
    _ = volume (A.chart i '' tsupport (ψ.χ i)) := lintegral_indicator_one hKm
    _ < ⊤ := hK.measure_lt_top

theorem vol_source_ne_zero (A : FinHolAtlas e X) (ψ : ChartPartition A) (j : Fin A.n)
    (hne : (A.chart j).source.Nonempty) : vol A ψ (A.chart j).source ≠ 0 := by
  have heq : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source = (A.chart j).target :=
    inter_eq_left.mpr fun y hy => (A.chart j).map_target hy
  rw [vol_apply_chart A ψ j (A.chart j).open_source.measurableSet subset_rfl, heq]
  intro h0
  rw [lintegral_eq_zero_iff' (((contDiffOn_dens A ψ j).continuousOn.aemeasurable
    (A.chart j).open_target.measurableSet).ennreal_ofReal)] at h0
  obtain ⟨x, hx⟩ := hne
  have hpos : 0 < volume (A.chart j).target :=
    (A.chart j).open_target.measure_pos volume ⟨A.chart j x, (A.chart j).map_source hx⟩
  have hF : ∀ᵐ y ∂(volume.restrict (A.chart j).target), False := by
    filter_upwards [h0, ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy1 hy2
    exact (ENNReal.ofReal_pos.mpr (dens_pos A ψ j hy2)).ne' hy1
  rw [ae_iff] at hF
  simp only [not_false_eq_true, ofPred_true, Measure.restrict_apply_univ] at hF
  exact hpos.ne' hF

theorem exists_isSmoothVolume [CompactSpace X] [T2Space X] [Nonempty X] (A : FinHolAtlas e X) :
    ∃ dV : Measure X, IsSmoothVolume A dV := by
  obtain ⟨ψ⟩ := GroundTheory.Heights₂.Heights.FourB.ChartPartitionExists.proof A
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨j0, hj0⟩ := A.cover x
  have hfin : vol A ψ univ ≠ ⊤ := by
    rw [vol, Measure.finsetSum_apply]
    exact (ENNReal.sum_lt_top.mpr fun i _ => piece_univ_lt_top A ψ i).ne
  have hpos : vol A ψ univ ≠ 0 := fun h =>
    vol_source_ne_zero A ψ j0 ⟨x, hj0⟩ (measure_mono_null (subset_univ _) h)
  refine ⟨(vol A ψ univ)⁻¹ • vol A ψ, ⟨?_⟩, fun j =>
    ⟨fun y => (vol A ψ univ).toReal⁻¹ * dens A ψ j y, ?_, ?_, ?_⟩⟩
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]
  · exact contDiffOn_const.mul (contDiffOn_dens A ψ j)
  · intro y hy
    exact mul_pos (inv_pos.mpr (ENNReal.toReal_pos hpos hfin)) (dens_pos A ψ j hy)
  · intro S hS hSj
    rw [Measure.smul_apply, smul_eq_mul, vol_apply_chart A ψ j hS hSj]
    simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hpos hfin), ENNReal.ofReal_toReal hfin]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel.ChartVolume
