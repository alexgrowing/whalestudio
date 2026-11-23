import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.D

section SlopeTestRemainingChoices

variable {U : Type} [CommRing U]

def mulQ (a : U) (n : ℕ) : U ⧸ Ideal.span {a ^ 1} →ₗ[U] U ⧸ Ideal.span {a ^ (n + 1)} :=
  Submodule.liftQ _ ((Ideal.span {a ^ (n + 1)}).mkQ ∘ₗ LinearMap.mulLeft U (a ^ n)) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    change Ideal.Quotient.mk _ (a ^ n * a ^ 1) = 0
    rw [pow_one, ← pow_succ]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))

theorem mulQ_mk (a : U) (n : ℕ) (x : U) :
    mulQ a n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (a ^ n * x) := rfl

theorem mulQ_inj (a : U) (ha : a ∈ nonZeroDivisors U) (n : ℕ) : Function.Injective (mulQ a n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mulQ_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, hc⟩ := hx
  refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨c, ?_⟩)
  have hn := pow_mem ha n
  rw [pow_succ, mul_comm (a ^ n) a, ← mul_assoc, mul_comm _ (a ^ n)] at hc
  rw [pow_one]
  exact (mul_cancel_left_mem_nonZeroDivisors hn).1 hc

theorem mulQ_exact (a : U) (n : ℕ) :
    Function.Exact (mulQ a n) (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow a n.le_succ))) := by
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Ideal.Quotient.mk _ c, by rw [mulQ_mk, mul_comm]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [mulQ_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hz
    obtain ⟨d, hd⟩ := hz
    exact ⟨c - d * a, by rw [sub_mul, mul_assoc, ← pow_succ', hd]; ring⟩

end SlopeTestRemainingChoices

end CrystallineSemistableComparison.D
