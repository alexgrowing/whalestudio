import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftNumberFieldModule
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_lift_number_field_module : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F)) →
    ∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by
  first | exact @GlobalTheory.nsmul_surj_of_card_torsion | exact GlobalTheory.nsmul_surj_of_card_torsion | (intros; apply GlobalTheory.nsmul_surj_of_card_torsion <;> assumption)
