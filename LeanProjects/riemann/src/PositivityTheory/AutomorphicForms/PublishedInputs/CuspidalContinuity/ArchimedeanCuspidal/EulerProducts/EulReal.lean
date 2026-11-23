import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.EulDefs
import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.GP

abbrev uniqueInfinitePlaceRat : Unique (InfinitePlace ℚ) :=
  ⟨⟨wR⟩, fun w => Subsingleton.elim w wR⟩

attribute [local instance] uniqueInfinitePlaceRat

theorem continuous_eR : Continuous eR :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal wR_isReal).continuous

theorem continuous_eR_symm : Continuous eR.symm :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal wR_isReal).symm.continuous

def eRu : (wR.Completion)ˣ ≃ₜ ℝˣ where
  toFun := Units.map eR.toRingHom.toMonoidHom
  invFun := Units.map eR.symm.toRingHom.toMonoidHom
  left_inv _ := Units.ext (eR.symm_apply_apply _)
  right_inv _ := Units.ext (eR.apply_symm_apply _)
  continuous_toFun := Units.continuous_map continuous_eR
  continuous_invFun := Units.continuous_map continuous_eR_symm

def aRh : (InfiniteAdeleRing ℚ)ˣ ≃ₜ ℝˣ :=
  (infiniteUnitsEquiv ℚ).toHomeomorph.trans
    ((Homeomorph.piUnique fun w : InfinitePlace ℚ => (w.Completion)ˣ).trans eRu)

theorem coe_aRh : (aRh : (InfiniteAdeleRing ℚ)ˣ → ℝˣ) = aR := by
  funext a
  exact Units.ext rfl

theorem measurableEmbedding_aR : MeasurableEmbedding aR := by
  rw [← coe_aRh]
  exact aRh.measurableEmbedding

theorem mult_wR : wR.mult = 1 := by
  rw [InfinitePlace.mult, if_pos wR_isReal]

theorem map_eRu : Measure.map eRu (infinitePlaceUnitsMeasure wR) = mulR := by
  set e := InfinitePlace.Completion.isometryEquivRealOfIsReal wR_isReal
  have he : ∀ y : ℝ, ‖e.symm y‖ = |y| := fun y => by
    have h0 : e.symm 0 = 0 := map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal wR_isReal).symm
    rw [e.symm.isometry.norm_map_of_map_zero h0, Real.norm_eq_abs]
  ext A hA
  have hpre : MeasurableSet (eRu ⁻¹' A) := eRu.continuous.measurable hA
  rw [Measure.map_apply eRu.continuous.measurable hA, infinitePlaceUnitsMeasure,
    unitsMeasure_apply _ _ hpre, infinitePlaceMeasure_of_isReal wR_isReal, mult_wR,
    MeasureTheory.setLIntegral_map (GroundTheory.Global.measurableEmbedding_units_val.measurableSet_image' hpre)
      (measurable_density_unitsMeasure 1) e.symm.continuous.measurable,
    mulR, GroundTheory.Global.measurableEmbedding_units_val.comap_apply,
    withDensity_apply _ (GroundTheory.Global.measurableEmbedding_units_val.measurableSet_image' hA)]
  have hset : e.symm ⁻¹' (Units.val '' (eRu ⁻¹' A)) = Units.val '' A := by
    ext y
    constructor
    · rintro ⟨u, hu, huy⟩
      refine ⟨eRu u, hu, ?_⟩
      change eR (u : wR.Completion) = y
      rw [huy]
      exact e.apply_symm_apply y
    · rintro ⟨r, hr, rfl⟩
      refine ⟨eRu.symm r, by simpa using hr, ?_⟩
      rfl
  rw [hset]
  refine setLIntegral_congr_fun (GroundTheory.Global.measurableEmbedding_units_val.measurableSet_image' hA) fun y _ => ?_
  rw [pow_one, he]

theorem map_aR : Measure.map aR (infiniteIdeleMeasure ℚ) = mulR := by
  have h1 : Measurable aR := measurableEmbedding_aR.measurable
  have h2 : Measurable (infiniteUnitsEquiv ℚ).symm := (infiniteUnitsEquiv ℚ).symm.continuous.measurable
  rw [infiniteIdeleMeasure, Measure.map_map h1 h2]
  have hc : aR ∘ (infiniteUnitsEquiv ℚ).symm =
      eRu ∘ (MeasurableEquiv.piUnique fun w : InfinitePlace ℚ => (w.Completion)ˣ) := by
    funext p
    exact Units.ext rfl
  rw [hc, ← Measure.map_map eRu.continuous.measurable (MeasurableEquiv.measurable _)]
  have hp := (measurePreserving_piUnique fun w : InfinitePlace ℚ => infinitePlaceUnitsMeasure w).map_eq
  convert congrArg (Measure.map eRu) hp using 2
  · exact (map_eRu).symm

end Ad3.GP
