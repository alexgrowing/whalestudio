import Mathlib

universe u_1

namespace Bl.general_b_fact_right_bis_other

theorem goal1 :
  ∀ {K : Type u_1} [inst : CommRing.{u_1} K] {n : Nat} {l l' : Matrix.{0, 0, u_1} (Fin n) (Fin n) K},
  (∀ (a b : Fin n), LT.lt.{0} a b → Eq.{u_1 + 1} (l a b) 0) →
    (∀ (a b : Fin n), LT.lt.{0} a b → Eq.{u_1 + 1} (l' a b) 0) →
      ∀ (a : Fin n), Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} l l' a a) (HMul.hMul.{u_1, u_1, u_1} (l a a) (l' a a)) := by
  intro K _ n l l' hl hl' a
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single a ?_ ?_
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hl' c a h, mul_zero]
    · rw [hl a c h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Bl.general_b_fact_right_bis_other
