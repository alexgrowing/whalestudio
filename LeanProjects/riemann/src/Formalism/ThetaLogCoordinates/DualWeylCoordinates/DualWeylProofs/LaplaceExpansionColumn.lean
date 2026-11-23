import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsMnTranspose

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_sr (R : Type*) [CommRing R] (A K : Finset (Fin n)) : R :=
  ∏ a ∈ A, ∏ k ∈ K, (if k < a then (-1 : R) else 1)

def wedgeSign (R : Type*) [CommRing R] (A K : Finset (Fin n)) : R := if Disjoint A K then ql_sr R A K else 0

def ql_w (R : Type*) [CommRing R] (A K I : Finset (Fin n)) : R := if A ∪ K = I then wedgeSign R A K else 0

variable {R : Type*} [CommRing R]

lemma ql_sr_union_left {A B : Finset (Fin n)} (h : Disjoint A B) (C : Finset (Fin n)) :
    ql_sr R (A ∪ B) C = ql_sr R A C * ql_sr R B C := prod_union h

lemma ql_sr_union_right (A : Finset (Fin n)) {B C : Finset (Fin n)} (h : Disjoint B C) :
    ql_sr R A (B ∪ C) = ql_sr R A B * ql_sr R A C := by
  simp only [ql_sr, prod_union h, prod_mul_distrib]

lemma ql_s_assoc (A B C : Finset (Fin n)) :
    wedgeSign R A B * wedgeSign R (A ∪ B) C = wedgeSign R B C * wedgeSign R A (B ∪ C) := by
  unfold wedgeSign
  by_cases hAB : Disjoint A B <;> by_cases hAC : Disjoint A C <;> by_cases hBC : Disjoint B C <;>
    simp only [disjoint_union_left, disjoint_union_right, hAB, hAC, hBC, if_true, if_false, and_true,
      and_false, and_self, mul_zero, zero_mul]
  rw [ql_sr_union_left hAB, ql_sr_union_right _ hBC]; ring

lemma ql_sr_single (A : Finset (Fin n)) (m : Fin n) : ql_sr R A {m} = ((qs_sg A m : ℤ) : R) := by
  simp only [ql_sr, prod_singleton, qs_sg]
  rw [prod_ite]; simp

lemma ql_sr_isUnit (A K : Finset (Fin n)) : IsUnit (ql_sr R A K) := by
  unfold ql_sr
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun a _ => ?_
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun k _ => ?_
  split_ifs
  · exact isUnit_one.neg
  · exact isUnit_one

lemma ql_s_isUnit {A K : Finset (Fin n)} (h : Disjoint A K) : IsUnit (wedgeSign R A K) := by
  rw [wedgeSign, if_pos h]; exact ql_sr_isUnit A K

lemma ql_sr_cast (A K : Finset (Fin n)) : ((ql_sr ℤ A K : ℤ) : R) = ql_sr R A K := by
  simp only [ql_sr, Int.cast_prod]
  refine prod_congr rfl fun a _ => prod_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma ql_s_cast (A K : Finset (Fin n)) : ((wedgeSign ℤ A K : ℤ) : R) = wedgeSign R A K := by
  unfold wedgeSign; split_ifs
  · exact ql_sr_cast A K
  · simp

lemma ql_w_cast (A K I : Finset (Fin n)) : ((ql_w ℤ A K I : ℤ) : R) = ql_w R A K I := by
  unfold ql_w; split_ifs
  · exact ql_s_cast A K
  · simp

lemma ql_sum_w (A K : Finset (Fin n)) (f : Finset (Fin n) → R) :
    ∑ I, f I * ql_w R A K I = wedgeSign R A K * f (A ∪ K) := by
  simp [ql_w, mul_comm]

lemma ql_w_assoc (A B C I : Finset (Fin n)) :
    ∑ M, ql_w R A B M * ql_w R M C I = ∑ M, ql_w R B C M * ql_w R A M I := by
  have h1 : ∑ M, ql_w R A B M * ql_w R M C I = wedgeSign R A B * ql_w R (A ∪ B) C I := by
    rw [← ql_sum_w A B (fun M => ql_w R M C I)]; exact sum_congr rfl fun _ _ => mul_comm _ _
  have h2 : ∑ M, ql_w R B C M * ql_w R A M I = wedgeSign R B C * ql_w R A (B ∪ C) I := by
    rw [← ql_sum_w B C (fun M => ql_w R A M I)]; exact sum_congr rfl fun _ _ => mul_comm _ _
  rw [h1, h2, ql_w, ql_w, union_assoc]
  split_ifs
  · exact ql_s_assoc A B C
  · simp

lemma ql_w_single (M I : Finset (Fin n)) (k : Fin n) :
    ql_w R M {k} I = if M = I.erase k then (if k ∈ I then ((qs_sg (I.erase k) k : ℤ) : R) else 0) else 0 := by
  by_cases hM : M = I.erase k
  · subst hM
    rw [if_pos rfl]
    by_cases hk : k ∈ I
    · have : I.erase k ∪ {k} = I := by
        rw [union_comm, ← insert_eq, insert_erase hk]
      rw [if_pos hk, ql_w, if_pos this, wedgeSign, if_pos (by simp), ql_sr_single]
    · rw [if_neg hk, ql_w, if_neg]
      intro h; exact hk (h ▸ mem_union_right _ (mem_singleton_self k))
  · rw [if_neg hM, ql_w]
    split_ifs with h
    · rw [wedgeSign, if_neg]
      intro hd
      apply hM
      rw [← h, union_comm, ← insert_eq, erase_insert (by simpa using hd)]
    · rfl

lemma sum_four_comm_form {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (F : α → β → γ → δ → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d := sum_congr rfl fun a _ => sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d := sum_congr rfl fun c _ => sum_congr rfl fun a _ => sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := sum_congr rfl fun c _ => sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := sum_congr rfl fun c _ => sum_congr rfl fun d _ => sum_comm

variable (g : Matrix (Fin n) (Fin n) R)

lemma laplace_expansion_column (B I : Finset (Fin n)) (m : Fin n) :
    ∑ M, ∑ k, qs_mn g M B * g k m * ql_w R M {k} I = wedgeSign R B {m} * qs_mn g I (B ∪ {m}) := by
  rw [sum_comm]
  have h1 : ∀ k, ∑ M, qs_mn g M B * g k m * ql_w R M {k} I =
      if k ∈ I then ((qs_sg (I.erase k) k : ℤ) : R) * qs_mn g (I.erase k) B * g k m else 0 := by
    intro k
    simp only [ql_w_single, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
    split_ifs
    · ring
    · rfl
  simp only [h1]
  rw [sum_ite_mem, univ_inter, qs_laplace_col, wedgeSign]
  by_cases hm : m ∈ B
  · rw [if_pos hm, if_neg (by simpa using hm), zero_mul]
  · rw [if_neg hm, if_pos (by simpa using hm), ql_sr_single, union_comm, ← insert_eq]

lemma ql_mn_empty (K : Finset (Fin n)) : qs_mn g K ∅ = if K = ∅ then 1 else 0 := by
  split_ifs with h
  · subst h; rw [qs_mn_eq g ∅ ∅ (h := 0) rfl rfl]; simp
  · exact qs_mn_ne g (by simpa using h)

lemma ql_s_empty (A : Finset (Fin n)) : wedgeSign R A ∅ = 1 := by simp [wedgeSign, ql_sr]

lemma ql_s_max {K : Finset (Fin n)} {m : Fin n} (h : ∀ x ∈ K, x < m) : wedgeSign R K {m} = 1 := by
  rw [wedgeSign, if_pos (by simpa using fun hm => lt_irrefl _ (h m hm)), ql_sr]
  refine prod_eq_one fun a ha => ?_
  rw [prod_singleton, if_neg (not_lt.2 (h a ha).le)]

theorem ql_lap (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' K * ql_w R A' K' I = wedgeSign R A K * qs_mn g I (A ∪ K) := by
  induction K using Finset.induction_on_max generalizing I with
  | empty =>
    simp only [ql_mn_empty, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true,
      ql_s_empty, one_mul, union_empty]
    simp [ql_w, ql_s_empty]
  | insert m K0 hmax ih =>
    have e1 : ∀ K', qs_mn g K' (insert m K0) = ∑ M, ∑ k, qs_mn g M K0 * g k m * ql_w R M {k} K' := by
      intro K'; rw [laplace_expansion_column, ql_s_max hmax, one_mul, union_comm, ← insert_eq]
    have h1 : ∀ A', ∑ K', qs_mn g A' A * qs_mn g K' (insert m K0) * ql_w R A' K' I =
        ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ K', ql_w R M {k} K' * ql_w R A' K' I := by
      intro A'
      simp only [e1, mul_sum, sum_mul]
      rw [sum_comm]; refine sum_congr rfl fun M _ => ?_
      rw [sum_comm]; exact sum_congr rfl fun k _ => sum_congr rfl fun K' _ => by ring
    have h2 : ∑ M', ∑ k, (∑ A', ∑ M, qs_mn g A' A * qs_mn g M K0 * ql_w R A' M M') * g k m * ql_w R M' {k} I =
        ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ M', ql_w R A' M M' * ql_w R M' {k} I := by
      simp only [mul_sum, sum_mul]
      rw [sum_four_comm_form]
      exact sum_congr rfl fun A' _ => sum_congr rfl fun M _ => sum_congr rfl fun k _ =>
        sum_congr rfl fun M' _ => by ring
    calc ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' (insert m K0) * ql_w R A' K' I
        = ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ K', ql_w R M {k} K' * ql_w R A' K' I :=
          sum_congr rfl fun A' _ => h1 A'
      _ = ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ M', ql_w R A' M M' * ql_w R M' {k} I :=
          sum_congr rfl fun A' _ => sum_congr rfl fun M _ => sum_congr rfl fun k _ => by rw [ql_w_assoc]
      _ = ∑ M', ∑ k, (wedgeSign R A K0 * qs_mn g M' (A ∪ K0)) * g k m * ql_w R M' {k} I := by
          rw [← h2]; simp only [ih]
      _ = wedgeSign R A K0 * ∑ M', ∑ k, qs_mn g M' (A ∪ K0) * g k m * ql_w R M' {k} I := by
          simp only [mul_sum, mul_assoc]
      _ = wedgeSign R A (insert m K0) * qs_mn g I (A ∪ insert m K0) := by
          rw [laplace_expansion_column, ← mul_assoc, ql_s_assoc, ql_s_max hmax, one_mul, union_assoc, union_comm K0, ← insert_eq]

theorem ql_lapT (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A A' * qs_mn g K K' * ql_w R A' K' I = ∑ I', ql_w R A K I' * qs_mn g I' I := by
  have h := ql_lap g.transpose A K I
  simp only [qs_mn_transpose] at h
  rw [h, ← ql_sum_w A K (fun I' => qs_mn g I' I)]
  exact sum_congr rfl fun _ _ => mul_comm _ _

theorem ql_lapM (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' K * ql_w R A' K' I = ∑ I', qs_mn g I I' * ql_w R A K I' := by
  rw [ql_lap, ql_sum_w A K (fun I' => qs_mn g I I')]

end Formalism.InvariantFactorPaths.ColumnFamilies
