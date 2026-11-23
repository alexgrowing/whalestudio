import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealCoprimeElementExists
import Mathlib
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractional_ideal_coprime_element_exists : ∀ {F : Type} [Field F] [NumberField F] (Y N : FractionalIdeal (𝓞 F)⁰ F), Y ≠ 0 → N ≠ 0 → N ≤ 1 →
    ∃ β ∈ Y, FractionalIdeal.spanSingleton (𝓞 F)⁰ β * Y⁻¹ + N = 1 := by
  first | exact @GlobalTheory.exists_mem_spanSingleton_mul_inv_add_eq_one | exact GlobalTheory.exists_mem_spanSingleton_mul_inv_add_eq_one | (intros; apply GlobalTheory.exists_mem_spanSingleton_mul_inv_add_eq_one <;> assumption)
