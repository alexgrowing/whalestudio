import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRootLeCardMulBoundOfEsymmNormLe
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_root_le_card_mul_bound_of_esymm_norm_le : ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), B.card = n → 1 ≤ M → (∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ M) → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ n * M := by
  first | exact @GlobalTheory.cauchy_roots_bound | exact GlobalTheory.cauchy_roots_bound | (intros; apply GlobalTheory.cauchy_roots_bound <;> assumption)
