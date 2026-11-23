import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotPowSmulBoundsDvrFgModule
import Mathlib
open Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_quot_pow_smul_bounds_dvr_fg_module : ∀ (O M : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup M] [Module O M] [Module.Finite O M] (t : O), t ≠ 0 → ¬ IsUnit t → (∀ r : ℕ, Finite (O ⧸ Ideal.span {t ^ r})) → ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M ≤ Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ∧ Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ≤ C * Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M := by
  first | exact @GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds | exact GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds | (intros; apply GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds <;> assumption)
