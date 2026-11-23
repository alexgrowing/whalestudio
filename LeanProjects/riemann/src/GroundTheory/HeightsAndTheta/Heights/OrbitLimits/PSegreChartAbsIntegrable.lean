import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartSheetCompare
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsPosDensMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffGradient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarIntAdd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm)
open ComplexSets Matrix

theorem SegreChartAbsIntegrable.proof (h₁ : SliceMassFinite.Statement)
    (h₂ : SegreChartSheetCompare.Statement) : SegreChartAbsIntegrable.Statement := by
  intro K _ _ ι _ P e m σ i L g _ hL hg J hJ A hA
  obtain ⟨M, hM⟩ := PtsPosDens.exists_bound hg
  obtain ⟨C, hC⟩ := h₂ K ι P e m σ i L hL
  have hJmin := mem_segreChartComponents.1 hJ
  have hℓ : linForm (Pi.single (σ.symm i) (1 : ℂ)) - 1 ∈ J := by
    rw [linForm_single]
    refine hJmin.1.2 ?_
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, -, hzi, rfl⟩
    simp [hzi]
  have hInt := h₁ m e (HermNorm.std m) J (Pi.single (σ.symm i) 1) A hJmin.1.1 hℓ
    (VarIntAdd.ringKrullDim_of_isFiniteProjection hA) hA
  set c : ℝ := max M 0 * max C 0 with hc
  have hmeas : Measurable (chartAbsDens J A (chartWeight σ i g) (chartPot σ i L)) :=
    SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
      ((continuous_mul.comp continuous_id).abs.measurable) (measurable_chartWeight σ i hg) _
  refine (hInt.const_mul c).mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (chartAbsDens_nonneg _ _ _ _ _)]
  refine sheetSum_le_mul (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y) c _ _ fun x hx s hs => ?_
  obtain ⟨hxJ, rfl⟩ := hx
  have hx1 : x (σ.symm i) = 1 := chart_coord_eq_one hJ hxJ
  have hG : |chartWeight σ i g x| ≤ max M 0 := by
    rw [chartWeight_of_coord g hx1]
    exact (hM _ (chartLift_blockNonzero σ i hx1)).trans (le_max_left _ _)
  have hD := hC J hJ A x s hxJ hs
  rw [abs_mul, one_mul, hc, mul_assoc]
  exact mul_le_mul hG (hD.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
    (abs_nonneg _) (le_max_right _ _)

end GroundTheory.Heights₂.Heights
