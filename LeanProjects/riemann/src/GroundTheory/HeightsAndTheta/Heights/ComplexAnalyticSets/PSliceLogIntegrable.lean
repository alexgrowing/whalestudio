import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFsLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutOffLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets Filter

noncomputable section

namespace SliceLogIntegrableProof

variable {n : ℕ}

theorem linEval_eq_one {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ x : Fin n → ℂ}
    (hx : x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) : linEval ℓ x = 1 := by
  have h1 := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (linForm ℓ - 1)))
  rw [map_sub, map_one, sub_eq_zero] at h1
  rw [← h1]
  simp [linForm, linEval]

theorem abs_le (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} {u ℓ x : Fin n → ℂ}
    (hx : x ∈ zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) :
    |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| ≤ |fsLog h u x| + |fsLog h ℓ x| := by
  have hℓ := linEval_eq_one hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [linEval] at hℓ
  have hd := (h.dualNorm_pos hx0).ne'
  have hfℓ : fsLog h ℓ x = -Real.log (h.dualNorm x) := by
    show Real.log (‖linEval ℓ x‖ / h.dualNorm x) = _
    rw [hℓ, norm_one, one_div, Real.log_inv]
  by_cases hu : linEval u x = 0
  · rw [hu, norm_zero, Real.log_zero, sub_zero, hfℓ, abs_neg]
    exact le_add_of_nonneg_left (abs_nonneg _)
  · have hfu : fsLog h u x = Real.log ‖linEval u x‖ - Real.log (h.dualNorm x) := by
      show Real.log (‖linEval u x‖ / h.dualNorm x) = _
      rw [Real.log_div (norm_ne_zero_iff.mpr hu) hd]
    rw [hfu, abs_sub_comm]
    exact le_add_of_nonneg_right (abs_nonneg _)

end SliceLogIntegrableProof

open SliceLogIntegrableProof in

theorem SliceLogIntegrable.proof (hG : SliceFsLogIntegrable.Statement) : SliceLogIntegrable.Statement := by
  classical
  intro n e h J F u ℓ A hJ hF hu hℓ hA
  obtain ⟨hprime, hdim, -⟩ := SliceIdeal.proof n (e + 1) J F ℓ hJ hF hℓ
  have hsm : SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) fun x => Real.log (h.dualNorm x) := by
    refine ⟨{x | x ≠ 0}, isOpen_ne, fun x hx hx0 => ?_, h.contDiffOn_log_dualNorm⟩
    have h1 := linEval_eq_one hx
    rw [hx0] at h1
    simp [linEval] at h1
  have hcu : Continuous fun x : Fin n → ℂ => linEval u x := by
    unfold linEval
    fun_prop
  have hcd : Continuous h.dualNorm := by
    unfold HermNorm.dualNorm
    fun_prop
  have hmeas : Measurable fun x : Fin n → ℂ => Real.log (h.dualNorm x) - Real.log ‖linEval u x‖ :=
    (Real.measurable_log.comp hcd.measurable).sub
      (Real.measurable_log.comp (continuous_norm.comp hcu).measurable)
  have hm := (SheetSumMeasurable.proof n (e + 1) _ A _ _ hprime hdim hA hmeas fun _ => hsm).2
  refine ((hG n e h J F u ℓ A hJ hF hu hℓ hA).add (hG n e h J F ℓ ℓ A hJ hF hℓ hℓ hA)).mono'
    hm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  simp only [Pi.add_apply, chartAbsDens, sheetSum]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun x _ => by split_ifs <;> positivity)]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs
  · rw [abs_mul, abs_mul, abs_mul, ← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_le h hx.1) (abs_nonneg _)
  · simp

end

end GroundTheory.Heights₂.Heights
