import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.CardQuotPow

open scoped TensorProduct
open GlobalTheory.TateLimit

theorem UpperTheory.V.K.cardKill :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Finite X] (c : ℕ) (Y : Submodule ℤ_[l] X), (∀ y ∈ Y, (l : ℤ_[l]) ^ c • y = 0) → Nat.card Y ≤ Nat.card (X ⧸ lpow l X 1) ^ c := by
  intro l _ X _ _ _ c Y hY
  refine le_trans ?_ (UpperTheory.V.K.cardQuotPow l X c)
  let f : X →ₗ[ℤ_[l]] X := LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ c)
  have hr : lpow l X c = LinearMap.range f := rfl
  have hYk : Y ≤ LinearMap.ker f := fun y hy => hY y hy
  have h1 : Nat.card Y ≤ Nat.card (LinearMap.ker f) :=
    Nat.card_le_card_of_injective (Submodule.inclusion hYk) (Submodule.inclusion_injective hYk)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h3 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h4 : Nat.card (X ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  rw [hr]
  refine h1.trans (le_of_eq (Nat.eq_of_mul_eq_mul_left hpos ?_))
  rw [h4] at h2
  rw [← h3, h2, mul_comm]
