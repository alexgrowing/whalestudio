import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeI
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcC
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsLocalHomeomorphStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDetIsFrameOnCanonicalWeightStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.EtaleMeasure

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

def rho (A : WeightedAtlas n Y ι La) (U : Set Y) (z : Y → V n) (x : U) : ℝ≥0∞ :=
  ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹

theorem rho_measurable (A : WeightedAtlas n Y ι La) {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) : Measurable (rho A U z) := by
  have hfr := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hE
  have hc : ContinuousOn (A.nsq A.kap (jdet A z)) U := api_nsq_contOn A hE.isOpen hfr.1
  have hc' : Continuous (fun x : U => A.nsq A.kap (jdet A z) x) := hc.restrict
  exact ENNReal.measurable_ofReal.comp hc'.measurable.inv

theorem mu_piece (A : WeightedAtlas n Y ι La) {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n (fun y : U => z y) e) (i : ι) (B : Set U)
    (hB : MeasurableSet B) (hBs : B ⊆ e.source) (hBi : ∀ m ∈ B, (m : Y) ∈ (A.chart i).source) :
    A.mu.comap Subtype.val B = ∫⁻ m in B, rho A U z m ∂vol n (fun y : U => z y) := by
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hemb := MeasurableEmbedding.subtype_coe hUm
  have hz : IsLocalHomeomorph (fun y : U => z y) := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  have hfr := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hE
  have hρ : Measurable (rho A U z) := rho_measurable A hE
  rw [hemb.comap_apply]
  have hBY : MeasurableSet (Subtype.val '' B : Set Y) := hemb.measurableSet_image.2 hB
  rw [A.mu_chart i _ hBY (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)]
  have hBimg : MeasurableSet (e '' B) := by
    have := measurableSet_image_of_chart n (fun y : U => z y) e he B hB hBs
    rwa [Set.image_congr fun m hm => he (hBs hm)] at this
  have hR : ∫⁻ m in B, rho A U z m ∂vol n (fun y : U => z y) =
      ∫⁻ w in e '' B, rho A U z (e.symm w) := by
    rw [← lintegral_indicator hB, lintegral_vol_chart n _ hz e he _ (hρ.indicator hB)
      (fun m hm => Set.indicator_of_notMem (fun h => hm (hBs h)) _)]
    have hsub : e '' B ⊆ e.target := fun _ ⟨m, hm, hmw⟩ => hmw ▸ e.map_source (hBs hm)
    rw [← Set.inter_eq_left.2 hsub, ← Measure.restrict_restrict hBimg, ← lintegral_indicator hBimg]
    refine setLIntegral_congr_fun e.open_target.measurableSet fun w hw => ?_
    by_cases h : e.symm w ∈ B
    · have hw' : w ∈ e '' B := ⟨e.symm w, h, e.right_inv hw⟩
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem hw']
    · have hw' : w ∉ e '' B := by
        rintro ⟨m, hm, rfl⟩
        exact h (by rw [e.left_inv (hBs hm)]; exact hm)
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem hw']
  set F : V n → V n := z ∘ (A.chart i).symm with hFdef
  set S := A.chart i '' (Subtype.val '' B)
  have hS : MeasurableSet S :=
    measurableSet_image_of_chart n (A.chart i) (A.chart i) (fun _ _ => rfl) _ hBY
      (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)
  have hOo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hSO : S ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨(A.chart i).map_source (hBi m hm), ?_⟩
    show (A.chart i).symm (A.chart i m) ∈ U
    rw [(A.chart i).left_inv (hBi m hm)]; exact m.2
  have hFm : ∀ m ∈ B, F (A.chart i m) = e m := fun m hm => by
    simp only [hFdef, Function.comp_apply, (A.chart i).left_inv (hBi m hm)]
    exact he (hBs hm)
  have himg : e '' B = F '' S := by
    rw [Set.image_image, Set.image_image]
    exact (Set.image_congr fun m hm => hFm m hm).symm
  have hinj : Set.InjOn F S := by
    rintro _ ⟨_, ⟨m1, hm1, rfl⟩, rfl⟩ _ ⟨_, ⟨m2, hm2, rfl⟩, rfl⟩ h
    rw [hFm m1 hm1, hFm m2 hm2] at h
    rw [e.injOn (hBs hm1) (hBs hm2) h]
  have hder : ∀ v ∈ S, HasFDerivWithinAt F
      ((fderiv ℂ F v).restrictScalars ℝ) S v := fun v hv =>
    ((((hE.holo i).differentiableAt (hOo.mem_nhds (hSO hv))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  rw [hR, himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hder hinj]
  refine setLIntegral_congr_fun hS ?_
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  have hmi := hBi m hm
  have hne : jdet A z i m ≠ 0 := hE.det_ne i m m.2 hmi
  have hns := api_nsq_eq A hfr.1 hmi m.2
  have hjd : (fderiv ℂ F (A.chart i m)).det = jdet A z i m := rfl
  simp only
  rw [hFm m hm, e.left_inv (hBs hm), (A.chart i).left_inv hmi, rho, ← hns,
    ← ENNReal.ofReal_mul (abs_nonneg _), fc_det_real, hjd]
  congr 1
  have h2 : 0 < ‖jdet A z i m‖ ^ 2 := by positivity
  rw [mul_inv, Real.exp_neg, inv_inv]
  field_simp

end

end GlobalTheory.EtaleMeasure

namespace GlobalTheory.EtaleMeasure

theorem lintegral_mu_etale : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ≥0∞, Measurable φ → ∫⁻ y in U, φ y ∂A.mu = ∫⁻ x : U, φ x * ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹ ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE φ hφ
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hz : IsLocalHomeomorph (fun y : U => z y) := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  have hρ : Measurable (rho A U z) := rho_measurable A hE
  have hmeas : A.mu.comap Subtype.val = (vol n (fun y : U => z y)).withDensity (rho A U z) := by
    choose e he hxe using fun x : U => exists_chart n _ hz x
    let W : U → Set U := fun x =>
      (e x).source ∩ Subtype.val ⁻¹' (A.chart (A.pick x)).source
    have hWo : ∀ x, IsOpen (W x) := fun x =>
      (e x).open_source.inter ((A.chart _).open_source.preimage continuous_subtype_val)
    obtain ⟨T, hTc, hTW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
    have huniv : ⋃ t : T, W t = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      have hx : x ∈ ⋃ i ∈ T, W i := hTW ▸ Set.mem_iUnion.2 ⟨x, hxe x, A.mem_pick _⟩
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, hxt⟩
    haveI := hTc.to_subtype
    refine Measure.ext_of_iUnion_eq_univ huniv fun t => ?_
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
      withDensity_apply _ (hB.inter (hWo t).measurableSet)]
    exact mu_piece A hE (e t) (he t) (A.pick (t : Y)) (B ∩ W t)
      (hB.inter (hWo t).measurableSet) (fun m hm => hm.2.1) (fun m hm => hm.2.2)
  rw [← lintegral_subtype_comap hUm, hmeas]
  exact (lintegral_withDensity_eq_lintegral_mul _ hρ (hφ.comp measurable_subtype_coe)).trans
    (lintegral_congr fun x => mul_comm _ _)

end GlobalTheory.EtaleMeasure
