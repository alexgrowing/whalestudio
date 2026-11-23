import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardKilledByIdealModIntEqAbsNormPow
import Mathlib
open scoped NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_killed_by_ideal_mod_int_eq_absNorm_pow : ∀ (K : Type) [Field K] [NumberField K] (M : Type) [AddCommGroup M] [Module (𝓞 K) M], Module.Free ℤ M → Module.Finite ℤ M → ∀ (r : ℕ), Module.finrank ℤ M = r * Module.finrank ℚ K → ∀ (𝔟 : Ideal (𝓞 K)) (c : ℕ), 0 < c → (c : 𝓞 K) ∈ 𝔟 → Nat.card {x : M ⧸ (Ideal.span {(c : 𝓞 K)} • (⊤ : Submodule (𝓞 K) M)) // ∀ a ∈ 𝔟, a • x = 0} = Ideal.absNorm 𝔟 ^ r := by
  first | (exact @GlobalTheory.TorsQuotCount.card_killed_eq) | (exact GlobalTheory.TorsQuotCount.card_killed_eq) | (intros; apply GlobalTheory.TorsQuotCount.card_killed_eq <;> assumption)
