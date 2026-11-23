import Mathlib

namespace GlobalTheory.CompanionTheory.LocalSubringUnits

theorem mem_prime_iff_not_inv_mem :
    ∀ {K : Type} [Field K] (T : Subring K) (P : Ideal T) (_ : P.IsPrime) (t : T),
      t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ (LocalSubring.ofPrime T P).toSubring) := by
  intro K _ T P hP t
  have key : IsUnit (algebraMap T (LocalSubring.ofPrime T P).toSubring t) ↔ t ∉ P :=
    IsLocalization.AtPrime.isUnit_to_map_iff (LocalSubring.ofPrime T P).toSubring P t
  have hcoe : ((algebraMap T (LocalSubring.ofPrime T P).toSubring t :
      (LocalSubring.ofPrime T P).toSubring) : K) = (t : K) := rfl
  constructor
  · rintro ht ⟨h0, hinv⟩
    refine key.1 (IsUnit.of_mul_eq_one ⟨(t : K)⁻¹, hinv⟩ ?_) ht
    apply Subtype.ext
    rw [Subring.coe_mul, hcoe]
    exact mul_inv_cancel₀ h0
  · intro h
    by_contra ht
    obtain ⟨u, hu⟩ := (key.2 ht).exists_right_inv
    have hu' : (t : K) * (u : K) = 1 := by
      have := congrArg (fun x : (LocalSubring.ofPrime T P).toSubring => (x : K)) hu
      simpa only [Subring.coe_mul, hcoe, Subring.coe_one] using this
    have h0 : (t : K) ≠ 0 := left_ne_zero_of_mul_eq_one hu'
    refine h ⟨h0, ?_⟩
    rw [inv_eq_of_mul_eq_one_right hu']
    exact u.2

end GlobalTheory.CompanionTheory.LocalSubringUnits
