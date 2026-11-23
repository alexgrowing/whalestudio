import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

theorem HermNorm.continuous_pointOf (h : HermNorm n) : Continuous h.pointOf := by
  unfold HermNorm.pointOf
  exact Continuous.matrix_mulVec continuous_const (continuous_pi fun i => by fun_prop)

theorem HermNorm.pointOf_eq_zero (h : HermNorm n) {y : EuclideanSpace ℂ (Fin n)}
    (hy : h.pointOf y = 0) : y = 0 := by
  have hu : IsUnit h.matᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_transpose]; exact h.isUnit_det)
  have hv : (fun i => y i) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hu (by simpa [HermNorm.pointOf] using hy)
  ext i
  simpa using congrFun hv i

theorem ConeIntegralLine.proof : ConeIntegralLine.Statement := by
  intro n h W y₀ hline φ hφ
  unfold coneIntegral
  set S := {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0} with hS
  have hSm : MeasurableSet S := by
    have hS' : S = {y | ‖y‖ < 1} ∩ ⋂ q ∈ W, {y | eval (h.pointOf y) q = 0} := by
      ext y; simp [S]
    rw [hS']
    exact (isOpen_lt continuous_norm continuous_const).measurableSet.inter
      (isClosed_biInter fun q _ =>
        isClosed_eq ((continuous_eval q).comp h.continuous_pointOf) continuous_const).measurableSet
  have h0 : Measure.hausdorffMeasure (((2 * (0 + 1) : ℕ) : ℝ))
      ({0} : Set (EuclideanSpace ℂ (Fin n))) = 0 := by
    have := hausdorffMeasure_of_dimH_lt (X := EuclideanSpace ℂ (Fin n)) (s := {0}) (d := 2)
      (by rw [dimH_singleton]; norm_num)
    simpa using this
  have hne : ∀ᵐ y ∂(Measure.hausdorffMeasure (((2 * (0 + 1) : ℕ) : ℝ)) :
      Measure (EuclideanSpace ℂ (Fin n))), y ≠ 0 := by
    rw [ae_iff]; simpa using h0
  have hae : ∀ᵐ y ∂(Measure.hausdorffMeasure (((2 * (0 + 1) : ℕ) : ℝ)) :
      Measure (EuclideanSpace ℂ (Fin n))), y ∈ S → φ (h.pointOf y) = φ y₀ := by
    filter_upwards [hne] with y hy hyS
    obtain ⟨t, ht⟩ := (hline _).1 hyS.2
    have htne : t ≠ 0 := by
      rintro rfl
      exact hy (h.pointOf_eq_zero (by simpa using ht))
    rw [ht, hφ t htne]
  rw [setIntegral_congr_ae hSm hae, setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  ring

end

end GroundTheory.Heights₂.Heights
