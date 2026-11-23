import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem pair_self_of_isIrrChar_algClosed (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G]
    (χ : G → L) (h : IsIrrChar L L χ) : pair χ χ = 1 := by
  classical
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : ρ.IsIrreducible := hρ

  have key := ρ.card_inv_mul_sum_char_mul_char_eq_finrank ρ
  rw [Representation.IsIrreducible.finrank_intertwiningMap_self] at key
  unfold pair
  rw [finsum_eq_sum_of_fintype]
  simp only [hχ, Algebra.algebraMap_self, RingHom.id_apply]
  simpa using key
end GlobalTheory.BI
