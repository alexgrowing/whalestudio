import Mathlib
import Formalism.GelfandTransference.Statement
import Formalism.GelfandTransference.GelfandCentral
import Formalism.GelfandTransference.HadamardGelfand.Gelfand

open Finset

namespace Formalism.HadamardInequality.P

section Highest

variable {A : Type} [Ring A] {n : ℕ}

theorem epow_succ_right (E : Fin n → Fin n → A) :
    ∀ (k : ℕ) (a b : Fin n), epow E (k + 1) a b = ∑ c, epow E k a c * E c b := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [epow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq]
  | succ k ih =>
    intro a b
    rw [show epow E (k + 1 + 1) a b = ∑ c, E a c * epow E (k + 1) c b from rfl]
    conv_lhs => enter [2, c]; rw [ih c b, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [show epow E (k + 1) a d = ∑ c, E a c * epow E k c d from rfl, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun c _ => (mul_assoc _ _ _).symm)

variable {M : Type} [AddCommGroup M] [Module A M]

theorem epow_upper_kill (E : Fin n → Fin n → A) (hE : GlRel E) (v : M)
    (hv : ∀ a b : Fin n, a < b → E a b • v = 0) :
    ∀ (k : ℕ) (a c : Fin n), a < c → epow E k a c • v = 0 := by
  intro k
  induction k with
  | zero =>
    intro a c hac
    simp [epow, ne_of_lt hac]
  | succ k ih =>
    intro a c hac
    rw [epow, Finset.sum_smul]
    refine Finset.sum_eq_zero (fun e _ => ?_)
    rw [mul_smul]
    by_cases hec : e < c
    · rw [ih e c hec, smul_zero]
    · have hae : a < e := lt_of_lt_of_le hac (not_lt.mp hec)
      have hcomm := comm_epow E hE k e c a e
      simp only [if_true, (ne_of_lt hac).symm, if_false, sub_zero] at hcomm
      have h1 : E a e * epow E k e c = epow E k e c * E a e + epow E k a c := by
        rw [← hcomm]; abel
      rw [← mul_smul, h1, add_smul, mul_smul, hv a e hae, smul_zero, zero_add, ih a c hac]

theorem epow_diag_smul_highest_weight (E : Fin n → Fin n → A) (hE : GlRel E) (ν : Fin n → ℤ) (v : M)
    (hv : ∀ a b : Fin n, a < b → E a b • v = 0) (hd : ∀ a : Fin n, E a a • v = ν a • v)
    (k : ℕ) (a : Fin n) :
    epow E (k + 1) a a • v =
      (ν a + (n : ℤ) - 1 - (a : ℤ)) • (epow E k a a • v) -
        ∑ b ∈ univ.filter (fun b : Fin n => a < b), epow E k b b • v := by
  set X : M := epow E k a a • v with hX
  have hterm : ∀ c : Fin n, epow E k a c • (E c a • v) =
      (if c = a then ν a • X else 0) +
        (if a < c then X - epow E k c c • v else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | hca | hca
    · rw [hv c a hca, smul_zero, if_neg (ne_of_lt hca), if_neg (not_lt.mpr (le_of_lt hca)),
        add_zero]
    · subst hca
      rw [if_pos rfl, if_neg (lt_irrefl _), add_zero, hd, hX, smul_comm]
    · rw [if_neg (ne_of_gt hca), if_pos hca, zero_add]
      have hcomm := comm_epow E hE k a c c a
      simp only [if_true] at hcomm
      have h1 : epow E k a c * E c a = E c a * epow E k a c - epow E k c c + epow E k a a := by
        have h2 := congrArg (fun t => E c a * epow E k a c - t) hcomm
        simp only [sub_sub_cancel] at h2
        rw [h2]; abel
      rw [← mul_smul, h1, add_smul, sub_smul, mul_smul, epow_upper_kill E hE v hv k a c hca,
        smul_zero, zero_sub, hX]
      abel
  rw [epow_succ_right, Finset.sum_smul]
  simp_rw [mul_smul, hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' univ a, if_pos (Finset.mem_univ a),
    ← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const]
  have hfil : univ.filter (fun b : Fin n => a < b) = Finset.Ioi a := by
    ext b; simp
  have hcard : (((Finset.Ioi a).card : ℕ) : ℤ) = (n : ℤ) - 1 - (a : ℤ) := by
    rw [Fin.card_Ioi]
    have := a.isLt
    omega
  rw [hfil, ← natCast_zsmul, hcard]
  simp only [sub_smul, add_smul]
  abel

theorem highest_weight_diagonal_holds : Formalism.HadamardInequality.HighestDiag := by
  intro A M _ _ _ n E hE ν v hv hd k a
  exact epow_diag_smul_highest_weight E hE ν v hv hd k a

end Highest

end Formalism.HadamardInequality.P
