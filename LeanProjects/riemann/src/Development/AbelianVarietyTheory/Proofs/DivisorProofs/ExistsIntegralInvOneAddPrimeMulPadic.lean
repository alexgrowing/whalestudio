import Mathlib
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_integral_inv_one_add_prime_mul :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (S : Type) [CommRing S] [Algebra ℤ_[ℓ] S] (s : S),
      IsIntegral ℤ_[ℓ] s → ∃ r : S, (1 + (ℓ : S) * s) * r = 1 ∧ IsIntegral ℤ_[ℓ] r := by
  intro ℓ _ S _ _ s hs
  let B := integralClosure ℤ_[ℓ] S
  let b : B := ⟨s, hs⟩
  have hu : IsUnit (1 + (ℓ : B) * b) := by
    by_contra hn
    obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hn)
    have hmax : (M.comap (algebraMap ℤ_[ℓ] B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have hl : (ℓ : ℤ_[ℓ]) ∈ M.comap (algebraMap ℤ_[ℓ] B) := by
      rw [heq, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at hl
    have h1 : (1 : B) ∈ M := by
      have := M.sub_mem hmem (M.mul_mem_right b hl)
      simpa using this
    exact hM.ne_top ((Ideal.eq_top_iff_one M).mpr h1)
  obtain ⟨r, hr⟩ := hu.exists_right_inv
  refine ⟨(r : S), ?_, r.2⟩
  have := congrArg (fun x : B => (x : S)) hr
  simpa [b] using this

end GlobalTheory
