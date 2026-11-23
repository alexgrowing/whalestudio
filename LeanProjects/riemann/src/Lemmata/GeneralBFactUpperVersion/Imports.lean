import Mathlib

namespace Bl.general_b_fact_upper_version

theorem goal1 :
  ∀ {R : Type} [inst : CommRing.{0} R] [IsDomain.{0} R] (ζ : R) (M : Nat) (P : Ideal.{0} R),
  Ne.{1} ζ 1 →
    Eq.{1} (HPow.hPow.{0, 0, 0} ζ M) 1 →
      Membership.mem.{0, 0} P (HSub.hSub.{0, 0, 0} ζ 1) → Membership.mem.{0, 0} P (Nat.cast.{0} M) := by
  intro R _ _ ζ M P h1 hM hP
  have hs : (∑ i ∈ Finset.range M, ζ ^ i) = 0 := by
    have h := geom_sum_mul ζ M
    rw [hM, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr h1)
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hP ⊢
  have h2 : Ideal.Quotient.mk P ζ = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at hP
    exact hP
  have h3 := congrArg (Ideal.Quotient.mk P) hs
  simpa [map_sum, map_pow, h2] using h3

end Bl.general_b_fact_upper_version
