import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicProductFormula
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_product_formula : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (a : K), a ≠ 0 → ∑ᶠ j : K →+* ℂ_[p], Real.log ‖j a‖ = -((padicValRat p (Algebra.norm ℚ a) : ℝ) * Real.log p) := by
  first | exact @GlobalTheory.sum_log_norm_embeddings_padicComplex | exact GlobalTheory.sum_log_norm_embeddings_padicComplex | (intros; apply GlobalTheory.sum_log_norm_embeddings_padicComplex <;> assumption)
