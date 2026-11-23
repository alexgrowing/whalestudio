import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.CasimirCoord

theorem sum_lt_sub : ∀ (n : ℕ) (f : Fin n → ℚ),
    ∑ i, ∑ j, (if i < j then f i - f j else 0) = ∑ i : Fin n, f i * ((n:ℚ) - 1 - 2 * ((i:ℕ):ℚ))
  | 0, f => by simp
  | n+1, f => by
    have h := sum_lt_sub n (fun i => f i.succ)
    simp only [Fin.sum_univ_succ, Fin.succ_lt_succ_iff, Fin.not_lt_zero, Fin.succ_pos, if_true, if_false,
      lt_irrefl, zero_add] at h ⊢
    rw [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e : ∑ i : Fin n, f i.succ * (((n+1:ℕ):ℚ) - 1 - 2 * ((i.succ:ℕ):ℚ))
        = ∑ i : Fin n, f i.succ * ((n:ℚ) - 1 - 2 * ((i:ℕ):ℚ)) - ∑ i : Fin n, f i.succ := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.val_succ]; push_cast; ring
    rw [e]; simp only [Fin.val_zero]; push_cast; ring

open Classical in
theorem casVal_eq_casK : ∀ (R S : ℕ) (μ : Ix R S → ℚ), GlobalTheory.BlockReps.casVal μ = GlobalTheory.RealLift.casK μ := by
  intro R S μ
  have hx : ∀ i j : Fin R, (if posC (Sum.inl i : Ix R S) (Sum.inl j) then μ (Sum.inl i) - μ (Sum.inl j) else 0)
      = if i < j then μ (Sum.inl i) - μ (Sum.inl j) else 0 := by
    intro i j; by_cases h : i < j
    · rw [if_pos (show posC (Sum.inl i : Ix R S) (Sum.inl j) from h), if_pos h]
    · rw [if_neg (show ¬ posC (Sum.inl i : Ix R S) (Sum.inl j) from h), if_neg h]
  have hy : ∀ i j : Fin S, (if posC (Sum.inr i : Ix R S) (Sum.inr j) then μ (Sum.inr i) - μ (Sum.inr j) else 0)
      = if i < j then μ (Sum.inr i) - μ (Sum.inr j) else 0 := by
    intro i j; by_cases h : i < j
    · rw [if_pos (show posC (Sum.inr i : Ix R S) (Sum.inr j) from h), if_pos h]
    · rw [if_neg (show ¬ posC (Sum.inr i : Ix R S) (Sum.inr j) from h), if_neg h]
  have hlr : ∀ (i : Fin R) (j : Fin S),
      (if posC (Sum.inl i : Ix R S) (Sum.inr j) then μ (Sum.inl i) - μ (Sum.inr j) else 0) = 0 :=
    fun i j => if_neg (show ¬ posC (Sum.inl i : Ix R S) (Sum.inr j) from id)
  have hrl : ∀ (i : Fin S) (j : Fin R),
      (if posC (Sum.inr i : Ix R S) (Sum.inl j) then μ (Sum.inr i) - μ (Sum.inl j) else 0) = 0 :=
    fun i j => if_neg (show ¬ posC (Sum.inr i : Ix R S) (Sum.inl j) from id)
  unfold GlobalTheory.BlockReps.casVal GlobalTheory.RealLift.casK
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← sq]
  rw [add_assoc]
  congr 1
  simp only [Fintype.sum_sum_type, hx, hy, hlr, hrl, Finset.sum_const_zero, add_zero, zero_add]
  rw [sum_lt_sub R (fun i => μ (Sum.inl i)), sum_lt_sub S (fun j => μ (Sum.inr j))]

end GlobalTheory.CasimirCoord
