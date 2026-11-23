import Mathlib

universe u_4

namespace Bl.FirstBlockLemmaB

theorem goal1 :
  ∀ {R : Type u_4} [inst : CommRing.{u_4} R] {P Q : Ideal.{u_4} R} [Ideal.IsPrime.{u_4} P],
  LE.le.{u_4} P Q →
    ∀ {x : R},
      Membership.mem.{u_4, u_4} Q x →
        Not (Membership.mem.{u_4, u_4} P x) →
          LE.le.{0} (HAdd.hAdd.{0, 0, 0} (ringKrullDim.{u_4} (HasQuotient.Quotient.{u_4, u_4} R Q)) 1)
            (ringKrullDim.{u_4} (HasQuotient.Quotient.{u_4, u_4} R P)) := by
  intro R _ P Q _ hPQ x hxQ hxP
  have hne : Ideal.Quotient.mk P x ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPQ)
    (Ideal.Quotient.factor_surjective hPQ) (r := Ideal.Quotient.mk P x)
    (mem_nonZeroDivisors_of_ne_zero hne) ?_
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact hxQ

end Bl.FirstBlockLemmaB
