import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardDivisorsLeAbsNormNumberField
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_divisors_le_absNorm_numberField : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ s : Finset (Ideal (𝓞 F)), (∀ J ∈ s, I ≤ J) → s.card ≤ Ideal.absNorm I := by
  first | exact @GlobalTheory.card_le_absNorm_of_forall_le | exact GlobalTheory.card_le_absNorm_of_forall_le | (intros; apply GlobalTheory.card_le_absNorm_of_forall_le <;> assumption)
