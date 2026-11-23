import Mathlib

namespace GlobalTheory.SchwartzDerivativeCompositionBound

theorem norm_iteratedFDeriv_schwartz_comp_clm_le
    {Y F : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Y →L[ℝ] F) (f : SchwartzMap F ℂ) (i : ℕ) (y : Y) :
    ‖iteratedFDeriv ℝ i (fun (z : Y) ↦ (f : F → ℂ) ((L : Y → F) z)) y‖ ≤
      ‖iteratedFDeriv ℝ i (⇑f : F → ℂ) ((L : Y → F) y)‖ * ‖L‖ ^ i := by
  have hf : ContDiff ℝ (i : ℕ) (⇑f : F → ℂ) := f.smooth i
  have h := L.iteratedFDeriv_comp_right hf y (i := i) le_rfl
  have e : (fun (z : Y) ↦ (f : F → ℂ) ((L : Y → F) z)) = (⇑f : F → ℂ) ∘ L := rfl
  rw [e, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp

end GlobalTheory.SchwartzDerivativeCompositionBound
