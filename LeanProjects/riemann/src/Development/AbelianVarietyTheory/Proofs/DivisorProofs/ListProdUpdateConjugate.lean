import Mathlib
open scoped ContDiff

namespace GlobalTheory

theorem list_prod_ofFn_update_mul_right (M : Type) [Group M] (k : ℕ) (f : Fin k → M)
    (j : Fin k) (y : M) :
    (List.ofFn (Function.update f j (f j * y))).prod =
      (List.ofFn f).prod * ((List.ofFn fun i => if j < i then f i else 1).prod⁻¹ * y *
        (List.ofFn fun i => if j < i then f i else 1).prod) := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j' => ?_) j
    · have h1 : ∀ i : Fin k, Function.update f 0 (f 0 * y) i.succ = f i.succ := fun i =>
        Function.update_of_ne (Fin.succ_ne_zero i) _ _
      have h2 : ∀ i : Fin k, (if (0 : Fin (k+1)) < i.succ then f i.succ else 1) = f i.succ :=
        fun i => if_pos (Fin.succ_pos i)
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [List.prod_cons, Function.update_self, h1, h2, lt_irrefl, if_false, one_mul]
      group
    · have h0 : Function.update f j'.succ (f j'.succ * y) 0 = f 0 :=
        Function.update_of_ne (Fin.succ_ne_zero j').symm _ _
      have h1 : ∀ i : Fin k, Function.update f j'.succ (f j'.succ * y) i.succ =
          Function.update (fun i => f i.succ) j' (f j'.succ * y) i := by
        intro i
        rcases eq_or_ne i j' with rfl | h
        · simp
        · rw [Function.update_of_ne (fun e => h (Fin.succ_injective _ e)),
            Function.update_of_ne h]
      have h2 : (if j'.succ < (0 : Fin (k+1)) then f 0 else 1) = 1 :=
        if_neg (Fin.not_lt_zero _)
      have h3 : ∀ i : Fin k, (if j'.succ < i.succ then f i.succ else 1) =
          (if j' < i then f i.succ else 1) := fun i => by
        simp only [Fin.succ_lt_succ_iff]
      have ih' := ih (fun i => f i.succ) j'
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [List.prod_cons, h0, h1, h2, h3, one_mul]
      rw [ih']
      simp only [mul_assoc]

end GlobalTheory
