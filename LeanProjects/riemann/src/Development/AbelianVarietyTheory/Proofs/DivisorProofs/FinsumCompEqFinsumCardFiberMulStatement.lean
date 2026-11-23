import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumCompEqFinsumCardFiberMul
import Mathlib
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_comp_eq_finsum_card_fiber_mul : ∀ {X Y : Type} (π : X → Y) (h : Y → ℂ), ((∀ y, h y ≠ 0 → (π ⁻¹' {y}).Finite) ∨ (∀ y, h y ≠ 0 → Nat.card (π ⁻¹' {y}) = 0)) → ∑ᶠ x, h (π x) = ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
  first | exact @GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul | exact GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul | (intros; apply GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul <;> assumption)
