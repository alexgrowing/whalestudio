import Mathlib
open scoped BigOperators

theorem UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute :
    ∀ (M : Type) [Monoid M] (r : ℕ) (a : Fin r → M), (∀ i j, i ≠ j → Commute (a i) (a j)) → ∀ i, (List.ofFn a).prod = a i * (List.ofFn (Function.update a i 1)).prod ∧ ∀ m : M, (∀ j, j ≠ i → Commute m (a j)) → Commute m (List.ofFn (Function.update a i 1)).prod := by
  intro M _ r a h i
  refine ⟨?_, ?_⟩
  · induction r with
    | zero => exact i.elim0
    | succ r ih =>
      refine Fin.cases ?_ (fun k => ?_) i
      · have h1 : (fun j : Fin r => Function.update a 0 1 j.succ) = fun j => a j.succ := by
          funext j
          rw [Function.update_of_ne (Fin.succ_ne_zero j)]
        rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, h1,
          Function.update_self, one_mul]
      · have h1 : (fun j : Fin r => Function.update a k.succ 1 j.succ)
            = Function.update (fun j : Fin r => a j.succ) k 1 := by
          funext j
          by_cases hj : j = k
          · subst hj
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hj,
              Function.update_of_ne (fun e => hj (Fin.succ_injective _ e))]
        have h2 := ih (fun j : Fin r => a j.succ)
          (fun i j hij => h _ _ (fun e => hij (Fin.succ_injective _ e))) k
        rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, h1,
          Function.update_of_ne (Fin.succ_ne_zero k).symm, h2, ← mul_assoc, ← mul_assoc,
          (h 0 k.succ (Fin.succ_ne_zero k).symm).eq]
  · intro m hm
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact Commute.one_right m
    · rw [Function.update_of_ne hj]
      exact hm j hj
