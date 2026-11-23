import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizationAwayFromPrime
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localization_away_from_prime : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∃ R : Subring F, IsPrincipalIdealRing R ∧
    ∀ x : F, x ∈ R ↔ ∃ s : ℕ, s.Coprime p ∧ IsIntegral ℤ ((s : F) * x) := by
  first | exact @GlobalTheory.exists_subring_pid_localization_coprime | exact GlobalTheory.exists_subring_pid_localization_coprime | (intros; apply GlobalTheory.exists_subring_pid_localization_coprime <;> assumption)
