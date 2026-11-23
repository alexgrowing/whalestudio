import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CancelArtinianNoetherianSummand
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cancel_artinian_noetherian_summand : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P], Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  first | exact @GlobalTheory.ks_cancel | exact GlobalTheory.ks_cancel | (intros; apply GlobalTheory.ks_cancel <;> assumption)
