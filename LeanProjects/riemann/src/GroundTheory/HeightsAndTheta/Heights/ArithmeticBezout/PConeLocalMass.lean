import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeLocalMass
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFiniteFibreDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal NNReal

noncomputable section

variable {n : ℕ}

def HermNorm.pointOfₗ (h : HermNorm n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) where
  toFun y := WithLp.toLp 2 (h.pointOf y)
  map_add' v w := by rw [HermNorm.pointOf_add']; rfl
  map_smul' c v := by rw [HermNorm.pointOf_smul']; rfl

theorem HermNorm.pointOfₗ_injective (h : HermNorm n) : Function.Injective h.pointOfₗ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  apply h.pointOf_eq_zero
  have := congrArg WithLp.ofLp hy
  simpa [HermNorm.pointOfₗ] using this

def HermNorm.pointOfL (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (LinearEquiv.ofInjectiveEndo h.pointOfₗ h.pointOfₗ_injective).toContinuousLinearEquiv

theorem mem_coneSet_iff_pointOfL (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (y : EuclideanSpace ℂ (Fin n)) : y ∈ coneSet h J ↔ h.pointOfL y ∈ zeroSetEuc J :=
  Iff.rfl

theorem hausdorffMeasure_coneSet_ball_le (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (d : ℕ) (R : ℝ) :
    Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coneSet h J ∩ Metric.ball 0 R) ≤
      ((‖(h.pointOfL.symm : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖₊ : ℝ≥0∞) ^
          ((2 * d : ℕ) : ℝ)) *
        Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSetEuc J ∩
          Metric.ball 0 (‖(h.pointOfL : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1)) := by
  set e := h.pointOfL
  have hsub : coneSet h J ∩ Metric.ball 0 R ⊆ e.symm '' (zeroSetEuc J ∩
      Metric.ball 0 (‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1)) := by
    rintro y ⟨hy, hyR⟩
    refine ⟨e y, ⟨(mem_coneSet_iff_pointOfL h J y).1 hy, ?_⟩, e.symm_apply_apply y⟩
    rw [mem_ball_zero_iff] at hyR ⊢
    calc ‖e y‖ = ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) y‖ := rfl
      _ ≤ ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R := by
        gcongr
      _ < _ := lt_add_one _
  calc _ ≤ Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (e.symm '' (zeroSetEuc J ∩
        Metric.ball 0 (‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1))) :=
        measure_mono hsub
    _ ≤ _ := e.symm.lipschitz.hausdorffMeasure_image_le (by positivity) _

theorem ConeLocalMass.proof (hDim : ConeFiniteFibreDim.Statement) (hMass : MassFinite.Statement)
    (hNull : NullSmaller.Statement) : ConeLocalMass.Statement := by
  intro n m h J hJ hm hmn hfib R
  have hle := hDim n m h J hJ hm hmn hfib
  refine lt_of_le_of_lt (hausdorffMeasure_coneSet_ball_le h J m R) ?_
  refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top) ?_
  rcases hle.lt_or_eq with hlt | heq
  · rw [measure_mono_null Set.inter_subset_left (hNull n m J hlt)]
    exact ENNReal.zero_lt_top
  · exact hMass n m J hJ.isPrime heq _

end

end GroundTheory.Heights₂.Heights
