import Mathlib
import Formalism.GelfandTransference.GelfandCentral

open Finset

namespace Formalism.HadamardInequality.P

variable {A : Type} [Ring A] {n : ℕ}

theorem comm_epow (E : Fin n → Fin n → A) (hE : GlRel E) (k : ℕ) :
    ∀ a b c d : Fin n, E c d * epow E k a b - epow E k a b * E c d =
      (if d = a then epow E k c b else 0) - (if b = c then epow E k a d else 0) := by
  induction k with
  | zero =>
    intro a b c d
    simp only [epow]
    by_cases hab : a = b <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
      subst_vars <;> simp_all <;> (intro h; subst h; simp_all)
  | succ k ih =>
    intro a b c d
    have key : ∀ e, E c d * (E a e * epow E k e b) - (E a e * epow E k e b) * E c d =
        (E c d * E a e - E a e * E c d) * epow E k e b +
          E a e * (E c d * epow E k e b - epow E k e b * E c d) := by
      intro e; noncomm_ring
    have h1 : ∀ e, E c d * E a e - E a e * E c d =
        (if d = a then E c e else 0) - (if e = c then E a d else 0) := fun e => hE c d a e
    simp only [epow]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [key, h1, ih]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hda : d = a <;> by_cases hbc : b = c <;> simp [hda, hbc] <;> abel

end Formalism.HadamardInequality.P
