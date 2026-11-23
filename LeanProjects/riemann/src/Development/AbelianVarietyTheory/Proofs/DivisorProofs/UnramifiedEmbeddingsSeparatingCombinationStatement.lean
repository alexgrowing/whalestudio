import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedEmbeddingsSeparatingCombination
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_embeddings_separating_combination : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 → ¬ p ∣ (NumberField.discr E).natAbs → ∀ σ : E →+* C, ∃ (n : ℕ) (a : Fin n → 𝓞 E) (c : Fin n → C), (∀ j, ‖c j‖ ≤ 1) ∧ ∑ j, c j * σ (a j : E) = 1 ∧ ∀ φ : E →+* C, φ ≠ σ → ∑ j, c j * φ (a j : E) = 0 := by
  first | exact @GlobalTheory.exists_integral_idempotent_of_not_dvd_discr | exact GlobalTheory.exists_integral_idempotent_of_not_dvd_discr | (intros; apply GlobalTheory.exists_integral_idempotent_of_not_dvd_discr <;> assumption)
