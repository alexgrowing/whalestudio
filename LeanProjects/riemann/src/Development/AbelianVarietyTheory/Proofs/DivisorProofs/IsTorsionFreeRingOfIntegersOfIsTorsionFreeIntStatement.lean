import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreeRingOfIntegersOfIsTorsionFreeInt
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorsionFree_ringOfIntegers_of_isTorsionFree_int' : ∀ (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.IsTorsionFree ℤ N], Module.IsTorsionFree (𝓞 E) N := by
  first | exact @GlobalTheory.isTorsionFree_ringOfIntegers_of_isTorsionFree_int | exact GlobalTheory.isTorsionFree_ringOfIntegers_of_isTorsionFree_int | (intros; apply GlobalTheory.isTorsionFree_ringOfIntegers_of_isTorsionFree_int <;> assumption)
