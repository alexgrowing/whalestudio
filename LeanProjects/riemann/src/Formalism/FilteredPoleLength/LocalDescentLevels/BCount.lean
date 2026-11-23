import Formalism.FilteredPoleLength.ReducedBasisBounds.ReductionQuotient

namespace Formalism.LatticeBaseChangeAlt

open Finset

theorem levelsSum : LevelsSum := by
  intro ι _ ep f mm v T c' h
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  have hf : (0 : ℝ) ≤ (f z : ℝ) := Nat.cast_nonneg _
  calc (mm z : ℝ) * f z ≤ (ep z * T * c' * v z) * f z := mul_le_mul_of_nonneg_right (h z) hf
    _ = T * c' * ((ep z : ℝ) * f z * v z) := by ring

noncomputable def slackEquiv (D k : ℕ) :
    {α : Fin D → ℕ // ∑ i, α i ≤ k} ≃ {β : Fin (D + 1) → ℕ // ∑ i, β i = k} where
  toFun α := ⟨Fin.cons (k - ∑ i, α.1 i) α.1, by
    have := α.2
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega⟩
  invFun β := ⟨Fin.tail β.1, by
    have := β.2
    rw [Fin.sum_univ_succ] at this
    simp only [Fin.tail]
    omega⟩
  left_inv α := by
    apply Subtype.ext
    simp only [Fin.tail_cons]
  right_inv β := by
    apply Subtype.ext
    have h := β.2
    rw [Fin.sum_univ_succ] at h
    have h0 : k - ∑ i, Fin.tail β.1 i = β.1 0 := by
      simp only [Fin.tail]
      omega
    simp only [h0, Fin.cons_self_tail]

end Formalism.LatticeBaseChangeAlt
