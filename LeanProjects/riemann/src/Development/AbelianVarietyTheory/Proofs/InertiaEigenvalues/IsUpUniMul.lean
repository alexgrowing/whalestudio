import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef

namespace GlobalTheory.UpperUnipotentMul

open Matrix

theorem isUpUni_mul {K : Type} [Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (hA : Formalism.MainNotions.S.IsUpUni A) (hB : Formalism.MainNotions.S.IsUpUni B) : Formalism.MainNotions.S.IsUpUni (A * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases lt_or_ge k i with hki | hik
    · rw [(hA i k).1 hki, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji hik), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hA i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem main : ∀ {K : Type} [inst : Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K},
    Formalism.MainNotions.S.IsUpUni A → Formalism.MainNotions.S.IsUpUni B → Formalism.MainNotions.S.IsUpUni (A * B) :=
  fun hA hB => isUpUni_mul hA hB

end GlobalTheory.UpperUnipotentMul
