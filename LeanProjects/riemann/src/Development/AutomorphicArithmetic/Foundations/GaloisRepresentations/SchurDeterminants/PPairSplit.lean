import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.pairSplit :
    PairSplit := by
  intro R _ n F i
  have hA : ∀ a : Fin n, ∏ b ∈ Ioi a, F a b =
      (∏ b ∈ (Ioi a).erase i, F a b) * (if a < i then F a i else 1) := by
    intro a
    split_ifs with h
    · exact (Finset.prod_erase_mul _ _ (by simpa using h)).symm
    · rw [Finset.erase_eq_self.mpr (by simpa using h), mul_one]
  have hL : ∏ a, ∏ b > a, F a b = ∏ a, ∏ b ∈ Ioi a, F a b := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rfl
  have h1 : (univ : Finset (Fin n)).filter (fun a => a < i) = (univ.erase i).filter (fun k => k < i) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, true_and, and_true]
    constructor
    · intro h; exact ⟨ne_of_lt h, h⟩
    · intro h; exact h.2
  have h2 : (univ.erase i).filter (fun k => ¬ k < i) = Ioi i := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, Finset.mem_Ioi, and_true, not_lt]
    constructor
    · intro h; exact lt_of_le_of_ne h.2 (Ne.symm h.1)
    · intro h; exact ⟨ne_of_gt h, le_of_lt h⟩
  rw [hL, Finset.prod_congr rfl fun a _ => hA a, Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase univ _ (Finset.mem_univ i),
    Finset.erase_eq_self.mpr (by simp), ← Finset.prod_filter, Finset.prod_ite, h1, h2]
  simp only [mul_comm, mul_left_comm, mul_assoc]
