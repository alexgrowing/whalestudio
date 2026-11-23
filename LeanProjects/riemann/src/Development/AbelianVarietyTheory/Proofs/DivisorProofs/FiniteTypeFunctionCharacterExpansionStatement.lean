import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFunctionCharacterExpansion
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_type_function_character_expansion : ∀ (G : Type) [Monoid G] (L : G → ℂ) (f : G → ℂ), f ∈ Submodule.span ℂ (Set.range fun p : (G →* ℂˣ) × ℕ => fun s : G => ((p.1 s : ℂˣ) : ℂ) * L s ^ p.2) → ∃ (N K : ℕ) (χ : Fin N → G →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ ∧ ∀ t, f t = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * L t ^ (k : ℕ) := by
  first | exact @GlobalTheory.exists_sum_distinct_chars_of_mem_span_char_mul_pow | exact GlobalTheory.exists_sum_distinct_chars_of_mem_span_char_mul_pow | (intros; apply GlobalTheory.exists_sum_distinct_chars_of_mem_span_char_mul_pow <;> assumption)
