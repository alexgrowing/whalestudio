import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetImageArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetImageAreaSet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

open scoped ENNReal

noncomputable section

theorem measurable_sheetJac {n d : ℕ} (s : (Fin d → ℂ) → Fin n → ℂ) : Measurable (sheetJac s) := by
  let C₁ : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap
  let C₂ : EuclideanSpace ℂ (Fin d) →L[ℝ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap
  have hΦ : Continuous fun M : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => C₁.comp (M.comp C₂) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  have h : sheetJac s = (fun M : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n) =>
      areaJacobian (M : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) ∘
      (fun M : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => C₁.comp (M.comp C₂)) ∘ fderiv ℝ s := by
    funext y
    rfl
  rw [h]
  exact (continuous_areaJacobian.comp hΦ).measurable.comp (measurable_fderiv ℝ s)

theorem SheetImageArea.proof (h : SheetImageAreaSet.Statement) : SheetImageArea.Statement := by
  classical
  intro n d A U s hU hs hA B hB hBU g hg
  let U' : Set (EuclideanSpace ℂ (Fin d)) := WithLp.ofLp ⁻¹' U
  let T : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := fun y => WithLp.toLp 2 (s (WithLp.ofLp y))
  let T' := U'.piecewise T (fun _ => 0)
  have hU' : IsOpen U' := hU.preimage (PiLp.continuous_ofLp 2 _)
  have hT : ContinuousOn T U' :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (hs.continuousOn.comp (PiLp.continuous_ofLp 2 _).continuousOn fun _ hy => hy)
  have hT'm : Measurable T' := hT.measurable_piecewise continuousOn_const hU'.measurableSet
  have hEq : ∀ y ∈ B, T' y = T y := fun y hy => Set.piecewise_eq_of_mem _ _ _ (hBU y hy)
  have hJ : Measurable fun y : EuclideanSpace ℂ (Fin d) => ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) :=
    ENNReal.measurable_ofReal.comp ((measurable_sheetJac s).comp (PiLp.continuous_ofLp 2 _).measurable)
  let ρ := (μH[((2 * d : ℕ) : ℝ)].restrict B).withDensity
    fun y : EuclideanSpace ℂ (Fin d) => ENNReal.ofReal (sheetJac s (WithLp.ofLp y))
  have hmap : ρ.map T' = (μH[((2 * d : ℕ) : ℝ)]).restrict (T '' B) := by
    ext S hS
    have hpre : MeasurableSet (T' ⁻¹' S) := hT'm hS
    rw [Measure.map_apply hT'm hS, withDensity_apply _ hpre, Measure.restrict_restrict hpre,
      Measure.restrict_apply hS,
      ← h n d A U s hU hs hA _ (hpre.inter hB) fun y hy => hBU y hy.2]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨hyS, hyB⟩, rfl⟩
      exact ⟨by simpa [Set.mem_preimage, hEq y hyB] using hyS, y, hyB, rfl⟩
    · rintro ⟨hzS, y, hyB, rfl⟩
      exact ⟨y, ⟨by simpa [Set.mem_preimage, hEq y hyB] using hzS, hyB⟩, rfl⟩
  calc ∫⁻ y in B, g (WithLp.toLp 2 (s (WithLp.ofLp y))) * ENNReal.ofReal (sheetJac s (WithLp.ofLp y))
          ∂(μH[((2 * d : ℕ) : ℝ)])
      = ∫⁻ y in B, ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) * g (T' y) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        setLIntegral_congr_fun hB fun y hy => by rw [hEq y hy, mul_comm]
    _ = ∫⁻ y, g (T' y) ∂ρ := (lintegral_withDensity_eq_lintegral_mul _ hJ (hg.comp hT'm)).symm
    _ = ∫⁻ z, g z ∂(ρ.map T') := (lintegral_map hg hT'm).symm
    _ = _ := by rw [hmap]

end

end GroundTheory.Heights₂.Heights
