import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIsotropicLeCard
import Mathlib

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_isotropic_le_card : ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] (L : Submodule K ((κ → K) × (κ → K))), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank K L ≤ Fintype.card κ := by
  first | exact @GlobalTheory.isotropic_finrank_le_card | exact GlobalTheory.isotropic_finrank_le_card | (intros; apply GlobalTheory.isotropic_finrank_le_card <;> assumption)
