import Mathlib

namespace GlobalTheory.NatMultipleRingOfIntegers

theorem exists_pos_nat_mul_mem_ringOfIntegers {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : NumberField.RingOfIntegers E, (b : E) = (m : E) * a := by
  have h1 : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  have hint' : IsIntegral ℤ ((y : E) * a) := by
    simpa [zsmul_eq_mul] using hint
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  have hm : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rcases Int.natAbs_eq y with h | h
    · have e : ((y.natAbs : ℕ) : E) = (y : E) := by
        conv_rhs => rw [h]
        exact (Int.cast_natCast _).symm
      rw [e]; exact hint'
    · have e : ((y.natAbs : ℕ) : E) = -(y : E) := by
        conv_rhs => rw [h]
        rw [Int.cast_neg, neg_neg, Int.cast_natCast]
      rw [e, neg_mul]; exact hint'.neg
  exact ⟨⟨_, hm⟩, rfl⟩

end GlobalTheory.NatMultipleRingOfIntegers
