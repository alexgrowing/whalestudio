import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnits

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.JR.UnitsHaar

theorem secondCountable_base (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] : SecondCountableTopology F := by
  haveI : LocallyCompactSpace F := @Unram.lcF F E _ _ _ _ ‹_›
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F (E := F)
  infer_instance

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E)

theorem top_K : T2Space A.K ∧ SecondCountableTopology A.K := by
  haveI := secondCountable_base F E
  let e := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : A.K ≃ₜ (Fin _ → F) := ⟨e.toEquiv, h1, h2⟩
  exact ⟨h.isEmbedding.t2Space, h.isEmbedding.isInducing.secondCountableTopology⟩

omit [Unram F E] in
theorem openUnits : IsOpenUnits A.K :=
  GlobalTheory.GaugeEx.isOpenUnits_of_basis (Module.finBasis F A.K)

omit [Unram F E] in
theorem absK_eq (t : A.K) : A.absK t = (GlobalTheory.GaugeEx.modu A.K t : ℝ) := by
  unfold Et.absK GlobalTheory.GaugeEx.modu; split_ifs <;> simp

omit [Unram F E] in
theorem borel_units : BorelSpace A.Kˣ := by
  have hemb := (openUnits A).isOpenEmbedding_unitsVal
  refine ⟨?_⟩
  rw [hemb.isEmbedding.isInducing.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
  rfl

omit [Unram F E] in
theorem modu_mul_left (c : A.Kˣ) (t : A.K) :
    GlobalTheory.GaugeEx.modu A.K ((c : A.K) * t) = GlobalTheory.GaugeEx.modu A.K c * GlobalTheory.GaugeEx.modu A.K t := by
  classical
  by_cases ht : IsUnit t
  · obtain ⟨u, rfl⟩ := ht
    rw [← Units.val_mul, GlobalTheory.GaugeEx.modu_units, GlobalTheory.GaugeEx.modu_units, GlobalTheory.GaugeEx.modu_units, map_mul]
  · have hct : ¬ IsUnit ((c : A.K) * t) := fun h => ht (IsUnit.mul_iff.1 h).2
    simp [GlobalTheory.GaugeEx.modu, ht, hct]

omit [Unram F E] in
theorem modu_units_inv (u : A.Kˣ) :
    (GlobalTheory.GaugeEx.modu A.K u)⁻¹ = distribHaarChar A.K u⁻¹ := by
  rw [GlobalTheory.GaugeEx.modu_units, map_inv]

def dens (t : A.K) : ℝ≥0 := (GlobalTheory.GaugeEx.modu A.K t)⁻¹

omit [Unram F E] in
theorem unitsMeas_eq (μK : Measure A.K) :
    LinDesc.unitsMeas A μK = (μK.withDensity fun t => (dens A t : ℝ≥0∞)).comap Units.val := by
  have : ∀ t, ENNReal.ofReal (A.absK t)⁻¹ = (dens A t : ℝ≥0∞) := fun t => by
    rw [absK_eq, dens, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  unfold LinDesc.unitsMeas
  simp only [this]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (μK : Measure A.K) (hμ : μK.IsAddHaarMeasure) :
    BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ,
      ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK := by
  classical
  obtain ⟨hT2, hSC⟩ := top_K A
  have hOU := openUnits A
  haveI hB := borel_units A
  have hemb := hOU.isOpenEmbedding_unitsVal
  have hme : MeasurableEmbedding (Units.val : A.Kˣ → A.K) := hemb.measurableEmbedding
  have hU : IsOpen {t : A.K | IsUnit t} := hemb.isOpen_range
  have hmod : Measurable (GlobalTheory.GaugeEx.modu A.K) := by
    have hc := (GlobalTheory.GaugeEx.modu_basic A.K).2.2.2 hOU
    have := hc.measurable_piecewise (g := fun _ => 0) continuousOn_const hU.measurableSet
    convert this using 1
    funext u
    by_cases hu : IsUnit u
    · simp [Set.piecewise, hu]
    · simp [Set.piecewise, GlobalTheory.GaugeEx.modu, hu]
  have hdm : Measurable (dens A) := hmod.inv
  set ν := μK.withDensity fun t => (dens A t : ℝ≥0∞) with hν
  rw [unitsMeas_eq]
  refine ⟨hB, ?_, ?_⟩
  swap
  · intro h
    have hr : Set.range (Units.val : A.Kˣ → A.K) = {t : A.K | IsUnit t} := Set.ext fun _ => Iff.rfl
    rw [← hme.integral_map, hme.map_comap, hr, restrict_withDensity hU.measurableSet,
      integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [NNReal.smul_def, Complex.real_smul, absK_eq, dens, NNReal.coe_inv, Complex.ofReal_inv, mul_comm]
  haveI := hμ
  have hc0 : ∀ c : A.Kˣ, 0 < GlobalTheory.GaugeEx.modu A.K c := fun c => ((GlobalTheory.GaugeEx.modu_basic A.K).1 c c.isUnit).1
  have hscale : ∀ (c : A.Kˣ) (G : A.K → ℝ≥0∞),
      ∫⁻ t, G t ∂μK = (GlobalTheory.GaugeEx.modu A.K c : ℝ≥0∞) * ∫⁻ t, G ((c : A.K) * t) ∂μK := by
    intro c G
    have e := ((GlobalTheory.GaugeEx.modu_basic A.K).1 c c.isUnit).2 μK hμ
    have hm : MeasurableEmbedding (fun z : A.K => (c : A.K) * z) := (Homeomorph.smul c).measurableEmbedding
    conv_lhs => rw [e]
    rw [lintegral_smul_measure, hm.lintegral_map]
    rfl
  have hinv : ∀ (c : A.Kˣ) (T : Set A.K), MeasurableSet T → ν ((fun t => (c : A.K) * t) ⁻¹' T) = ν T := by
    intro c T hT
    have hT' : MeasurableSet ((fun t => (c : A.K) * t) ⁻¹' T) := (measurable_const_mul _) hT
    rw [hν, withDensity_apply _ hT, withDensity_apply _ hT', ← lintegral_indicator hT, ← lintegral_indicator hT']
    conv_rhs => rw [hscale c]
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine lintegral_congr fun t => ?_
    by_cases ht : (c : A.K) * t ∈ T
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ (fun t => (c : A.K) * t) ⁻¹' T from ht)]
      rw [← ENNReal.coe_mul, ENNReal.coe_inj, dens, dens, modu_mul_left, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (hc0 c).ne', one_mul]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show t ∉ (fun t => (c : A.K) * t) ⁻¹' T from ht),
        mul_zero]
  have hL : (ν.comap Units.val).IsMulLeftInvariant := by
    refine ⟨fun c => ?_⟩
    ext S hS
    rw [Measure.map_apply (measurable_const_mul c) hS, hme.comap_apply, hme.comap_apply]
    have hset : Units.val '' ((fun x => c * x) ⁻¹' S) = (fun t : A.K => (c : A.K) * t) ⁻¹' (Units.val '' S) := by
      ext t; constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨c * u, hu, Units.val_mul c u⟩
      · rintro ⟨s, hs, hst⟩
        refine ⟨c⁻¹ * s, by simpa [Set.mem_preimage] using hs, ?_⟩
        rw [Units.val_mul, hst, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [hset, hinv c _ (hme.measurableSet_image.2 hS)]
  have hF : IsFiniteMeasureOnCompacts (ν.comap Units.val) := by
    refine ⟨fun C hC => ?_⟩
    rw [hme.comap_apply]
    have hcont : Continuous fun u : A.Kˣ => distribHaarChar A.K u⁻¹ :=
      (GlobalTheory.GaugeEx.continuous_distribHaarChar_units A.K).comp continuous_inv
    obtain ⟨M, hM⟩ := (hC.image hcont).bddAbove
    have hC' : IsCompact (Units.val '' C) := hC.image Units.continuous_val
    calc ν (Units.val '' C) = ∫⁻ t in Units.val '' C, (dens A t : ℝ≥0∞) ∂μK :=
          withDensity_apply _ hC'.measurableSet
      _ ≤ ∫⁻ t in Units.val '' C, (M : ℝ≥0∞) ∂μK := by
          refine setLIntegral_mono measurable_const fun t ht => ?_
          obtain ⟨u, hu, rfl⟩ := ht
          rw [ENNReal.coe_le_coe, dens, modu_units_inv]
          exact hM ⟨u, hu, rfl⟩
      _ = M * μK (Units.val '' C) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hC'.measure_lt_top
  have hP : (ν.comap Units.val).IsOpenPosMeasure := by
    refine ⟨fun U hUo hne => ?_⟩
    rw [hme.comap_apply]
    have hVo : IsOpen (Units.val '' U) := hemb.isOpenMap U hUo
    intro h0
    rw [hν, withDensity_apply _ hVo.measurableSet, lintegral_eq_zero_iff hdm.coe_nnreal_ennreal] at h0
    have h1 : ∀ᵐ t ∂(μK.restrict (Units.val '' U)), False := by
      filter_upwards [h0, ae_restrict_mem hVo.measurableSet] with t ht hV
      obtain ⟨u, -, rfl⟩ := hV
      have : (dens A u : ℝ≥0∞) ≠ 0 := by
        rw [ENNReal.coe_ne_zero, dens, modu_units_inv]; exact distribHaarChar_pos.ne'
      exact this (by simpa using ht)
    have h2 : μK.restrict (Units.val '' U) = 0 := ae_eq_bot.1 (eventually_false_iff_eq_bot.1 h1)
    rw [Measure.restrict_eq_zero] at h2
    exact (hVo.measure_pos μK (hne.image _)).ne' h2
  exact { toIsFiniteMeasureOnCompacts := hF, toIsMulLeftInvariant := hL, toIsOpenPosMeasure := hP }

end GlobalTheory.JR.UnitsHaar

namespace GlobalTheory.JR.LinDesc

theorem unitsMeas_isHaar : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ, ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK :=
  fun _ _ _ _ _ _ _ A μK hμ => GlobalTheory.JR.UnitsHaar.finiteRing_sq_sub_mul_sq_eq_of_card A μK hμ

end GlobalTheory.JR.LinDesc
