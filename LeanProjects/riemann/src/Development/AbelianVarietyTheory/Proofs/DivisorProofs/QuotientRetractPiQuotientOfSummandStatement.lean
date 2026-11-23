import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientRetractPiQuotientOfSummand
import Mathlib
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_retract_pi_quotient_of_summand : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
  [Module.Finite C H] [Module.Projective C H] (F : Submodule C H), I • ⊤ ≤ F →
  (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
  ∃ (m : ℕ) (s : (H ⧸ F) →ₗ[C] (Fin m → C ⧸ I)) (r : (Fin m → C ⧸ I) →ₗ[C] (H ⧸ F)),
    r ∘ₗ s = LinearMap.id := by
  first | exact @GlobalTheory.quotient_retract_pi_quotient | exact GlobalTheory.quotient_retract_pi_quotient | (intros; apply GlobalTheory.quotient_retract_pi_quotient <;> assumption)
