import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FrameMeasStatementPfC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up.MI ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable FM.haarF FM.haarIx

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem FrameMeasStatement_holds : FrameMeasStatement (E := E) := by
  intro r X x0 hx0 C hC hCd
  have hx0' : X.IsOrtho x0 := hx0
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  obtain ⟨R1, hR1⟩ := β0_bound (X := X) hC hCd
  have hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ max R1 0 :=
    fun x hx τ a b => (hR1 x hx τ a b).trans (le_max_left _ _)
  have hKR : KR X (max R1 0) ≠ ⊤ := (KR_lt_top (X := X) (le_max_right R1 0)).ne
  have hdet : ∀ τ, (mat x0 τ).det ≠ 0 := by
    intro τ h
    have h1 := normSq_det_orthogonalFrame (X := X) hx0' τ
    rw [h, map_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hU0 : ((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have hΦ0 : ((Measure.addHaarScalarFactor (volume.map (ΦC X)) volume : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have hP : (∏ τ, (mat x0 τ).det ^ r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (hdet τ)
  have hA0 : ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (Complex.normSq_pos.mpr hP))).ne'
  refine ⟨((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹ *
      (ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹)⁻¹ * KR X (max R1 0) *
      ((Measure.addHaarScalarFactor (volume.map (ΦC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹, ?_, ?_⟩
  · exact (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr hU0) (ENNReal.inv_ne_top.mpr hA0)) hKR)
      (ENNReal.inv_ne_top.mpr hΦ0)).lt_top
  intro G hGm hGinv
  have hFm : Measurable (C.indicator G) := hGm.indicator hCm
  have hφm : Measurable ({p | Jp X C p ≠ 0}.indicator G) :=
    hGm.indicator ((measurable_Jp (X := X) hCm) (measurableSet_singleton 0).compl)

  have hUf : ∫⁻ v, C.indicator G (ufC X v) =
      ((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ x, C.indicator G x := lintegral_ufC (X := X) (C.indicator G)
  have hLA : ∫⁻ v, C.indicator G (ufC X (LA (fun τ => mat x0 τ) v)) =
      ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹ *
        ∫⁻ v, C.indicator G (ufC X v) :=
    lintegral_comp_LA (fun τ => mat x0 τ) hdet (hFm.comp (ufC X).continuous.measurable)
  have hgm : Measurable (fun v => C.indicator G (ufC X (LA (fun τ => mat x0 τ) v))) :=
    hFm.comp ((ufC X).continuous.measurable.comp
      (LinearMap.continuous_of_finiteDimensional _).measurable)
  have hin : ∫⁻ v, C.indicator G (ufC X (LA (fun τ => mat x0 τ) v)) ≤
      KR X (max R1 0) * ∫⁻ x, GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x := by
    refine le_trans (le_of_eq (lintegral_flat hgm)) ?_
    rw [← lintegral_const_mul' _ _ hKR]
    exact lintegral_mono fun x => inner_le (X := X) hx0' hCm hCd hR0 hGinv x
  have hmuX := lintegral_muX (X := X) (x0 := x0) hφm
  have hlast : ∫⁻ z, ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) ∂muX X x0 ≤
      ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0 := by
    have hpt : ∀ z, ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) ≤
        (sat X x0 C).indicator (fun z => G (cpt X x0 z)) z := by
      intro z
      by_cases hJ : Jp X C (cpt X x0 z) = 0
      · have h0 : ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) = 0 :=
          Set.indicator_apply_eq_zero.mpr fun h => (h hJ).elim
        rw [h0]
        exact zero_le
      · have hz : z ∈ sat X x0 C := by
          by_contra hz
          apply hJ
          apply Jp_eq_zero (X := X)
          intro y hy hyC
          exact hz (mem_sat (X := X) hCd hy hyC)
        rw [Set.indicator_of_mem (show cpt X x0 z ∈ {p | Jp X C p ≠ 0} from hJ),
          Set.indicator_of_mem hz]
    exact (lintegral_mono hpt).trans (lintegral_indicator_le _ _)
  have e1 : ∫⁻ x, C.indicator G x =
      ((Measure.addHaarScalarFactor (volume.map (ufC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹ *
        ∫⁻ v, C.indicator G (ufC X v) := by
    rw [hUf, ← mul_assoc, ENNReal.inv_mul_cancel hU0 ENNReal.coe_ne_top, one_mul]
  have e2 : ∫⁻ v, C.indicator G (ufC X v) =
      (ENNReal.ofReal (Complex.normSq (∏ τ, (mat x0 τ).det ^ r))⁻¹)⁻¹ *
        ∫⁻ v, C.indicator G (ufC X (LA (fun τ => mat x0 τ) v)) := by
    rw [hLA, ← mul_assoc, ENNReal.inv_mul_cancel hA0 ENNReal.ofReal_ne_top, one_mul]
  have e4 : ∫⁻ x, GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x =
      ((Measure.addHaarScalarFactor (volume.map (ΦC X)) volume : ℝ≥0) : ℝ≥0∞)⁻¹ *
        ∫⁻ z, ({p | Jp X C p ≠ 0}.indicator G) (cpt X x0 z) ∂muX X x0 := by
    rw [hmuX, ← mul_assoc, ENNReal.inv_mul_cancel hΦ0 ENNReal.coe_ne_top, one_mul]
  rw [← lintegral_indicator (f := G) hCm, e1, e2, mul_assoc, mul_assoc, mul_assoc]
  gcongr
  refine hin.trans ?_
  rw [e4]
  gcongr
  all_goals exact hlast

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
