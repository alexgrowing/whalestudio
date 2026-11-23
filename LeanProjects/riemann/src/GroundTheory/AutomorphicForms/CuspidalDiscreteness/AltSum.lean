import Mathlib

open Finset

namespace GroundTheory.Automorphic

def altSum {V W : Type*} [AddCommGroup V] [AddCommGroup W] :
    (k : ℕ) → (V → W) → (Fin k → V) → V → W
  | 0, h, _, s => h s
  | k + 1, h, y, s => altSum k (fun t => h (t + y 0) - h t) (Fin.tail y) s

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

@[simp] theorem altSum_zero (h : V → W) (y : Fin 0 → V) (s : V) : altSum 0 h y s = h s := rfl

theorem altSum_succ (k : ℕ) (h : V → W) (y : Fin (k + 1) → V) (s : V) :
    altSum (k + 1) h y s = altSum k (fun t => h (t + y 0) - h t) (Fin.tail y) s := rfl

def altSign {k : ℕ} (ε : Fin k → Bool) : ℤ := ∏ i, if ε i then 1 else -1

def altPoint {k : ℕ} (y : Fin k → V) (ε : Fin k → Bool) : V := ∑ i, if ε i then y i else 0

theorem altSum_eq_sum : ∀ (k : ℕ) (h : V → W) (y : Fin k → V) (s : V),
    altSum k h y s = ∑ ε : Fin k → Bool, altSign ε • h (s + altPoint y ε)
  | 0, h, y, s => by simp [altSign, altPoint]
  | k + 1, h, y, s => by
    rw [altSum_succ, altSum_eq_sum k, ← (Fin.consEquiv fun _ => Bool).sum_comp,
      Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ε _ => ?_
    simp only [Fin.consEquiv_apply, altSign, altPoint, Fin.prod_univ_succ, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ, if_true, Bool.false_eq_true, if_false, one_mul, zero_add,
      Fin.tail]
    rw [smul_sub, neg_mul, one_mul, neg_smul, add_comm (y 0), ← add_assoc]
    abel

end GroundTheory.Automorphic
