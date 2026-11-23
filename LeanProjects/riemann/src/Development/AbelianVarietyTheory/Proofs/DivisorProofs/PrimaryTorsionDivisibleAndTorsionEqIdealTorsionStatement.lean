import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimaryTorsionDivisibleAndTorsionEqIdealTorsion
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primaryTorsion_divisible_and_torsion_eq_ideal_torsion : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (g : ℕ) (I : Ideal (𝓞 E)), g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → (∀ x : M, ∃ y : M, g • y = x) → (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → ∃ y : M, g • y = x ∧ ∀ a ∈ I ^ (j + 1), a • y = 0) ∧ (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → g • x = 0 → ∀ a ∈ I, a • x = 0) := by
  first | exact @GlobalTheory.primaryTorsion_divisible_and_gTorsion | exact GlobalTheory.primaryTorsion_divisible_and_gTorsion | (intros; apply GlobalTheory.primaryTorsion_divisible_and_gTorsion <;> assumption)
