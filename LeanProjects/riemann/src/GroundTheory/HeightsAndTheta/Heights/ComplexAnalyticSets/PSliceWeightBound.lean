import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceWeightBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffGradient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

theorem SliceWeightBound.proof (hL : SliceLogIntegrable.Statement) : SliceWeightBound.Statement := by
  classical
  intro n e h J F u ℓ hJ hF hu hℓ
  set S := J ⊔ Ideal.span {linForm ℓ - 1} with hS
  set g : (Fin n → ℂ) → ℝ := fun x => Real.log (h.dualNorm x) - Real.log ‖linEval u x‖ with hg
  set φ : Fin (e + 1) → (Fin n → ℂ) → ℝ := fun _ x => Real.log (h.dualNorm x) with hφ
  by_cases hA : ∃ A : Matrix (Fin (e + 1)) (Fin n) ℂ, IsFiniteProjection S A
  · refine ⟨∫ y, chartAbsDens S hA.choose g φ y, fun w M _ hwM => ?_⟩
    have hM : 0 ≤ M := (abs_nonneg _).trans (hwM 0)
    have hint := hL n e h J F u ℓ hA.choose hJ hF hu hℓ hA.choose_spec
    have hpt : ∀ y, ‖chartDens S hA.choose (fun x => g x * w x) φ y‖ ≤
        M * chartAbsDens S hA.choose g φ y := by
      intro y
      refine (Real.norm_eq_abs _ ▸ abs_chartDens_le _ _ _ _ y).trans ?_
      refine sheetSum_le_mul (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA.choose_spec y) M _ _ ?_
      intro x _ s _
      rw [abs_mul, abs_mul, abs_mul]
      have := hwM x
      calc |g x| * |w x| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|
          = |w x| * (|g x| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|) := by ring
        _ ≤ M * (|g x| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|) :=
          mul_le_mul_of_nonneg_right this (by positivity)
    have hb := norm_integral_le_of_norm_le (hint.const_mul M) (Filter.Eventually.of_forall hpt)
    rw [integral_const_mul, Real.norm_eq_abs] at hb
    simp only [varInt, dif_pos hA, chartInt]
    linarith
  · refine ⟨0, fun w M _ hwM => ?_⟩
    simp only [varInt, dif_neg hA, abs_zero, zero_mul, le_refl]

end

end GroundTheory.Heights₂.Heights
