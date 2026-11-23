import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationSpanEqIdOnIrreducible
import Mathlib
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_augmentationSpan_eq_id_on_irreducible : ∀ {K : Type} [Field K] [IsAlgClosed K] {Γ : Type} [Group Γ] {m : ℕ} (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)), (∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P) → (∀ Q : Submodule K (Fin m → K), Q ≤ P → (∀ g, ∀ v ∈ Q, S g *ᵥ v ∈ Q) → Q = ⊥ ∨ Q = P) → (∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v) → ∃ T ∈ Submodule.span K (Set.range fun g => S g - 1), ∀ v ∈ P, T *ᵥ v = v := by
  first | exact @GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on | exact GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on | (intros; apply GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on <;> assumption)
