import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSliceSeminormLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_slice_seminorm_le : ∀ {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ), ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by
  first | exact @GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le | exact GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le | (intros; apply GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le <;> assumption)
