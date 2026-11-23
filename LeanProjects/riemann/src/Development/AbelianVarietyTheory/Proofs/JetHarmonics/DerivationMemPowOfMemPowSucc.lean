import Mathlib

namespace GlobalTheory.DerivationMemPow

theorem derivation_mem_pow_of_mem_pow_succ {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (D : Derivation k A A) (I : Ideal A) (n : ℕ) :
    ∀ x ∈ I ^ (n + (1 : ℕ)), (D : A → A) x ∈ I ^ n := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ ?_
      · exact Ideal.mul_mem_right _ _ ha
      · have h := Ideal.mul_mem_mul hb (ih a ha)
        rwa [← pow_succ'] at h
    · intro y z hy hz
      rw [map_add]
      exact Ideal.add_mem _ hy hz

example : ∀ {k A : Type} [inst : CommRing k] [inst_1 : CommRing A] [inst_2 : Algebra k A] (D : Derivation k A A) (I : Ideal A) (n : ℕ), ∀ x ∈ I ^ (n + (1 : ℕ)), (D : A → A) x ∈ I ^ n :=
  fun D I n => derivation_mem_pow_of_mem_pow_succ D I n

end GlobalTheory.DerivationMemPow
