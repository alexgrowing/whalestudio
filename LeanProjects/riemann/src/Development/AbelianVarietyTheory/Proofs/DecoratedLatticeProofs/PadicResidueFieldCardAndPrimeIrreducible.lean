import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open ValuativeRel IsLocalRing

noncomputable section

namespace GlobalTheory.TAdicInt

def intEquiv (T : ℕ) [Fact T.Prime] : 𝒪[ℚ_[T]] ≃+* ℤ_[T] where
  toFun x := ⟨x.1, by
    have h := (Valuation.mem_integer_iff _ _).1 x.2
    have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff T 1 x.1).not.1 (by rw [map_one]; exact not_lt.2 h)
    rwa [norm_one, not_lt] at this⟩
  invFun x := ⟨x.1, (Valuation.mem_integer_iff _ _).2 (by
    have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff T 1 x.1).not.2 (by rw [norm_one]; exact not_lt.2 x.2)
    rwa [map_one, not_lt] at this)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem card_residueField (T : ℕ) [Fact T.Prime] : Nat.card (ResidueField 𝒪[ℚ_[T]]) = T := by
  rw [Nat.card_congr ((ResidueField.mapEquiv (intEquiv T)).trans PadicInt.residueField).toEquiv, Nat.card_zmod]

theorem irreducible_natCast (T : ℕ) [Fact T.Prime] : Irreducible (T : 𝒪[ℚ_[T]]) := by
  have := (PadicInt.irreducible_p (p := T)).map (intEquiv T).symm.toMulEquiv
  rwa [show (intEquiv T).symm.toMulEquiv (T : ℤ_[T]) = (T : 𝒪[ℚ_[T]]) from
    map_natCast (intEquiv T).symm T] at this

theorem card_residueField_and_irreducible :
    ∀ (T : ℕ) [Fact T.Prime], Nat.card (IsLocalRing.ResidueField 𝒪[ℚ_[T]]) = T ∧
      Irreducible ((T : 𝒪[ℚ_[T]])) :=
  fun T _ => ⟨card_residueField T, irreducible_natCast T⟩

end GlobalTheory.TAdicInt
