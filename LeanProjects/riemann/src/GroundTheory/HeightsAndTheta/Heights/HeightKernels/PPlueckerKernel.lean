import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem PlueckerKernel.proof (h₁ : PlueckerNormSq.Statement) (h₂ : PlueckerUnitBound.Statement) :
    PlueckerKernel.Statement := by
  intro j m Z hZ
  set S : ℝ := ∑ I : {I : Finset (Fin (j + m)) // I.card = j}, ‖(colsOf (onePipe Z) I).det‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun I _ => by positivity
  have hnorm : ‖((S : ℝ) : ℂ)‖ = S := Complex.norm_of_nonneg hS0
  have heq : ((S : ℝ) : ℂ) = (1 + Z * Zᴴ).det := h₁ j m Z
  calc S = ‖((S : ℝ) : ℂ)‖ := hnorm.symm
    _ = ‖(1 + Z * Zᴴ).det‖ := by rw [heq]
    _ ≤ (1 + m : ℝ) ^ j := h₂ j m Z hZ

end GroundTheory.Heights₂.Heights
