import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.ClaimOf

open Polynomial

noncomputable section

open Classical

namespace PI.SqfRootsInj.W

open PI.SqfLab

theorem lp_pow_four_le {g r e ℓ : ℕ} (hℓ : ℓ.Prime) (hB : ℓ ∉ BB r g) (h1 : 1 ≤ e)
    (h2 : e ≤ r) : (Lp g e ℓ) ^ 4 ≤ g ^ e := by
  by_contra h
  push_neg at h
  apply hB
  right
  refine ⟨e, h1, h2, hℓ, ?_⟩
  unfold Lp at h
  rwa [← pow_mul, mul_comm] at h

theorem two_pow_card_primeFactors_le {n : ℕ} (hn : n ≠ 0) : 2 ^ n.primeFactors.card ≤ n := by
  calc 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

theorem card_nthRoots_toFinset_le {K : Type*} [Field K] (N : ℕ) (a : K) :
    (nthRoots N a).toFinset.card ≤ N :=
  (Multiset.toFinset_card_le _).trans (card_nthRoots N a)

theorem card_roots_X_pow_sub_X_le {K : Type*} [Field K] (M : ℕ) (hM : 2 ≤ M) :
    ((X ^ M - X : K[X]).roots.toFinset).card ≤ M := by
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp <;> omega

end PI.SqfRootsInj.W
