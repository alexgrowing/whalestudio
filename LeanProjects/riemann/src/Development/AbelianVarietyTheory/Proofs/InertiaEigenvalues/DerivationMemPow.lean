import Mathlib

namespace GlobalTheory.DerivationPowerIdeal

theorem derivation_mem_pow {A' : Type} [CommRing A'] {k : Type} [CommRing k] [Algebra k A']
    (I : Ideal A') (D : Derivation k A' A') (n : ℕ) {x : A'} (hx : x ∈ I ^ (n + 1)) :
    D x ∈ I ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' I (n + 1)] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hb)
      rw [pow_succ' I n]
      exact Ideal.mul_mem_mul ha (ih hb)
    · intro a b ha hb
      rw [map_add]
      exact Ideal.add_mem _ ha hb

end GlobalTheory.DerivationPowerIdeal
