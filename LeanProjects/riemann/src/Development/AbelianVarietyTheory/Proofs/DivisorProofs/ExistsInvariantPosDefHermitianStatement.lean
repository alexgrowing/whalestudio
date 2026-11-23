import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPosDefHermitian
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact : ∀ {n : ℕ} (H : Subgroup (GL (Fin n) ℂ)), IsCompact (H : Set (GL (Fin n) ℂ)) →
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * g = P := by
  first | exact @GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian | exact GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian | (intros; apply GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian <;> assumption)
