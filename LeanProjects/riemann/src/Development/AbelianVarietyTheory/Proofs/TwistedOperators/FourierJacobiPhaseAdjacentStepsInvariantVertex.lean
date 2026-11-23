import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseUnipotentVolumeConjDiagonalEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.PhaseStep

open GlobalTheory.DiagVol

section Shape
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mul_apply_of_shape {β : Type} {ℓ : ι → ℕ} {M : Matrix ι ι k}
    (hM : ∀ r s, ℓ s ≤ ℓ r → M r s = (1 : Matrix ι ι k) r s) (D : Matrix ι β k) (r : ι) (s : β) :
    (M * D) r s = D r s + ∑ t, if ℓ r < ℓ t then M r t * D t s else 0 := by
  rw [Matrix.mul_apply]
  have h : ∀ t, M r t * D t s = (if t = r then D t s else 0) + (if ℓ r < ℓ t then M r t * D t s else 0) := by
    intro t
    by_cases ht : ℓ r < ℓ t
    · have : t ≠ r := by rintro rfl; exact lt_irrefl _ ht
      simp [ht, this]
    · rw [hM r t (by omega), if_neg ht, add_zero]
      by_cases htr : t = r
      · subst htr; simp
      · rw [Matrix.one_apply_ne (Ne.symm htr), if_neg htr, zero_mul]
  rw [Finset.sum_congr rfl fun t _ => h t, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem apply_mul_of_shape {α : Type} {ℓ : ι → ℕ} {M : Matrix ι ι k}
    (hM : ∀ r s, ℓ s ≤ ℓ r → M r s = (1 : Matrix ι ι k) r s) (D : Matrix α ι k) (r : α) (s : ι) :
    (D * M) r s = D r s + ∑ t, if ℓ t < ℓ s then D r t * M t s else 0 := by
  rw [Matrix.mul_apply]
  have h : ∀ t, D r t * M t s = (if t = s then D r t else 0) + (if ℓ t < ℓ s then D r t * M t s else 0) := by
    intro t
    by_cases ht : ℓ t < ℓ s
    · have : t ≠ s := by rintro rfl; exact lt_irrefl _ ht
      simp [ht, this]
    · rw [hM t s (by omega), if_neg ht, add_zero]
      by_cases htr : t = s
      · subst htr; simp
      · rw [Matrix.one_apply_ne htr, if_neg htr, mul_zero]
  rw [Finset.sum_congr rfl fun t _ => h t, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

end Shape

section Step
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}

theorem stepPt_rr_lt (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (l : Fin c) (i : Fin (c + 1))
    (h : i.val < l.val) : stepPt x₀ e (.inr l) (.inr i) = 0 := by
  have h1 : ¬ (Free (c / 2 + 1) ((Sum.inr l : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1))) ∨
      Kept ((Sum.inr l : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1)))) := by
    simp only [Free, Kept, or_false]; omega
  rw [stepPt, Matrix.add_apply, Matrix.of_apply, dif_neg h1, add_zero, basePt, fromBlocks_apply₂₂,
    Matrix.of_apply, if_neg (by omega)]

theorem stepPt_rr_eq (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (l : Fin c) (i : Fin (c + 1))
    (h : l.val = i.val) : stepPt x₀ e (.inr l) (.inr i) = 1 := by
  have h1 : ¬ (Free (c / 2 + 1) ((Sum.inr l : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1))) ∨
      Kept ((Sum.inr l : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1)))) := by
    simp only [Free, Kept, or_false]; omega
  rw [stepPt, Matrix.add_apply, Matrix.of_apply, dif_neg h1, add_zero, basePt, fromBlocks_apply₂₂,
    Matrix.of_apply, if_pos h]

theorem stepPt_lr_zero (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (r : n) (i : Fin (c + 1))
    (h : i.val < c / 2 ∨ (i.val = c / 2 ∧ c % 2 = 1)) : stepPt x₀ e (.inl r) (.inr i) = 0 := by
  have h1 : ¬ (Free (c / 2 + 1) ((Sum.inl r : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1))) ∨
      Kept ((Sum.inl r : n ⊕ Fin c), (Sum.inr i : n' ⊕ Fin (c + 1)))) := by
    simp only [Free, Kept, Nat.even_iff]; omega
  rw [stepPt, Matrix.add_apply, Matrix.of_apply, dif_neg h1, add_zero, basePt, fromBlocks_apply₁₂,
    Matrix.zero_apply]

theorem stepPt_rl_zero (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (l : Fin c) (s : n')
    (h : c / 2 < l.val ∨ (l.val = c / 2 ∧ c % 2 = 0)) : stepPt x₀ e (.inr l) (.inl s) = 0 := by
  have h1 : ¬ (Free (c / 2 + 1) ((Sum.inr l : n ⊕ Fin c), (Sum.inl s : n' ⊕ Fin (c + 1))) ∨
      Kept ((Sum.inr l : n ⊕ Fin c), (Sum.inl s : n' ⊕ Fin (c + 1)))) := by
    simp only [Free, Kept, Nat.odd_iff]; omega
  rw [stepPt, Matrix.add_apply, Matrix.of_apply, dif_neg h1, add_zero, basePt, fromBlocks_apply₂₁,
    Matrix.zero_apply]

end Step

section Ch
variable {k : Type} [Field k] {n n₀ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n] [DecidableEq n]
  [Fintype n₂] [DecidableEq n₂] {c : ℕ}

theorem sum_succ_eq (f : Fin (c + 1) → Fin (c + 1) → k) :
    (∑ i : Fin (c + 1), ∑ j : Fin (c + 1), if j.val = i.val + 1 then f i j else 0) =
      ∑ l : Fin c, f l.castSucc l.succ := by
  rw [Fin.sum_univ_castSucc]
  have h0 : (∑ j : Fin (c + 1), if j.val = (Fin.last c).val + 1 then f (Fin.last c) j else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => if_neg (by simp; omega)
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l.succ]
  · rw [if_pos (by simp)]
  · intro j _ hj; rw [if_neg]; intro h; exact hj (Fin.ext (by simp at h ⊢; omega))
  · simp

theorem ch_shape_mul {M : Matrix (n ⊕ Fin (c + 1)) (n ⊕ Fin (c + 1)) k}
    (hM : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → M r s = (1 : Matrix _ _ k) r s)
    (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) :
    ch (M * stepPt x₀ e₀) = ch (stepPt x₀ e₀) + ∑ l : Fin c, M (.inr l.castSucc) (.inr l.succ) +
      ∑ i : Fin (c + 1), if 2 * i.val + 1 = c then
        ∑ x, M (.inr i) (.inl x) * stepPt x₀ e₀ (.inl x) (.inr i.succ) else 0 := by
  unfold ch
  rw [Finset.sum_congr rfl fun i _ => mul_apply_of_shape hM (stepPt x₀ e₀) _ _, Finset.sum_add_distrib]
  refine Eq.trans (congrArg (_ + ·) ?_) (add_assoc _ _ _).symm
  have key : ∀ i : Fin (c + 1), (∑ t : n ⊕ Fin (c + 1), if ordL (c + 1) (Sum.inr i : n ⊕ Fin (c + 1)) < ordL (c + 1) t then
      M (.inr i) t * stepPt x₀ e₀ t (.inr i.succ) else 0) =
      (∑ j : Fin (c + 1), if j.val = i.val + 1 then M (.inr i) (.inr j) else 0) +
      (if 2 * i.val + 1 = c then ∑ x, M (.inr i) (.inl x) * stepPt x₀ e₀ (.inl x) (.inr i.succ) else 0) := by
    intro i
    rw [Fintype.sum_sum_type, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j.val = i.val + 1
      · rw [if_pos (by simp [ordL]; omega), if_pos hj, stepPt_rr_eq _ _ _ _ (by simp [hj]), mul_one]
      · rw [if_neg hj]
        split_ifs with h
        · rw [stepPt_rr_lt _ _ _ _ (by simp [ordL] at h; simp; omega), mul_zero]
        · rfl
    · by_cases hc : 2 * i.val + 1 = c
      · rw [if_pos hc]
        exact Finset.sum_congr rfl fun x _ => if_pos (by simp [ordL]; omega)
      · rw [if_neg hc]
        refine Finset.sum_eq_zero fun x _ => ?_
        split_ifs with h
        · rw [stepPt_lr_zero _ _ _ _ (by simp [ordL] at h; simp; omega), mul_zero]
        · rfl
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, sum_succ_eq]

theorem ch_mul_shape {M : Matrix (n ⊕ Fin (c + 1)) (n ⊕ Fin (c + 1)) k}
    (hM : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → M r s = (1 : Matrix _ _ k) r s)
    (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k) :
    ch (stepPt x₁ e₁ * M) = ch (stepPt x₁ e₁) + ∑ l : Fin c, M (.inr l.castSucc) (.inr l.succ) +
      ∑ l : Fin c, if 2 * l.val + 1 = c then
        ∑ x, stepPt x₁ e₁ (.inr l) (.inl x) * M (.inl x) (.inr l.succ) else 0 := by
  unfold ch
  rw [Finset.sum_congr rfl fun i _ => apply_mul_of_shape hM (stepPt x₁ e₁) _ _, Finset.sum_add_distrib]
  refine Eq.trans (congrArg (_ + ·) ?_) (add_assoc _ _ _).symm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fintype.sum_sum_type, add_comm]
  congr 1
  · rw [Finset.sum_eq_single l.castSucc]
    · rw [if_pos (by simp [ordL]), stepPt_rr_eq _ _ _ _ (by simp), one_mul]
    · intro j _ hj
      split_ifs with h
      · rw [stepPt_rr_lt _ _ _ _ ?_, zero_mul]
        simp [ordL] at h
        have : j.val ≠ l.val := fun h' => hj (Fin.ext (by simp [h']))
        omega
      · rfl
    · simp
  · by_cases hc : 2 * l.val + 1 = c
    · rw [if_pos hc]
      exact Finset.sum_congr rfl fun x _ => if_pos (by simp [ordL]; omega)
    · rw [if_neg hc]
      refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs with h
      · rw [stepPt_rl_zero _ _ _ _ (by simp [ordL] at h; omega), zero_mul]
      · rfl

end Ch

section Rel
variable {k : Type} [Field k] {n n₀ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n] [DecidableEq n]
  [Fintype n₂] [DecidableEq n₂] {c : ℕ} {V W : Matrix (n ⊕ Fin (c + 1)) (n ⊕ Fin (c + 1)) k}

theorem simple_rel (hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → V r s = (1 : Matrix _ _ k) r s)
    (hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → W r s = (1 : Matrix _ _ k) r s) (hVW : V * W = 1) (l : Fin c) :
    V (.inr l.castSucc) (.inr l.succ) + W (.inr l.castSucc) (.inr l.succ) +
      (if 2 * l.val + 1 = c then ∑ x, V (.inr l.castSucc) (.inl x) * W (.inl x) (.inr l.succ) else 0) = 0 := by
  have h := congrFun (congrFun hVW (.inr l.castSucc)) (.inr l.succ)
  rw [mul_apply_of_shape hV W, Matrix.one_apply_ne (by simp [Fin.ext_iff]), Fintype.sum_sum_type] at h
  have h1 : (∑ j : Fin (c + 1), if ordL (c + 1) (Sum.inr l.castSucc : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inr j : n ⊕ Fin (c + 1)) then
      V (.inr l.castSucc) (.inr j) * W (.inr j) (.inr l.succ) else 0) = V (.inr l.castSucc) (.inr l.succ) := by
    rw [Finset.sum_eq_single l.succ]
    · rw [if_pos (by simp [ordL]), hW _ _ le_rfl, Matrix.one_apply_eq, mul_one]
    · intro j _ hj
      split_ifs with hc
      · rw [hW _ _ (by simp [ordL] at hc ⊢; omega), Matrix.one_apply_ne (by simpa using hj), mul_zero]
      · rfl
    · simp
  have h2 : (∑ x : n, if ordL (c + 1) (Sum.inr l.castSucc : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inl x : n ⊕ Fin (c + 1)) then
      V (.inr l.castSucc) (.inl x) * W (.inl x) (.inr l.succ) else 0) =
      (if 2 * l.val + 1 = c then ∑ x, V (.inr l.castSucc) (.inl x) * W (.inl x) (.inr l.succ) else 0) := by
    by_cases hc : 2 * l.val + 1 = c
    · rw [if_pos hc]
      exact Finset.sum_congr rfl fun x _ => if_pos (by simp [ordL]; omega)
    · rw [if_neg hc]
      refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs with h'
      · rw [hW _ _ (by simp [ordL] at h' ⊢; omega), Matrix.one_apply_ne (by simp), mul_zero]
      · rfl
  rw [h1, h2] at h
  linear_combination h

theorem row_rel (hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → V r s = (1 : Matrix _ _ k) r s)
    (hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → W r s = (1 : Matrix _ _ k) r s) (hVW : V * W = 1)
    (hc : c % 2 = 1) (x : n) :
    V (.inr ⟨c / 2, by omega⟩) (.inl x) + W (.inr ⟨c / 2, by omega⟩) (.inl x) = 0 := by
  have h := congrFun (congrFun hVW (.inr ⟨c / 2, by omega⟩)) (.inl x)
  rw [mul_apply_of_shape hV W, Matrix.one_apply_ne (by simp), Fintype.sum_sum_type] at h
  have h1 : (∑ j : Fin (c + 1), if ordL (c + 1) (Sum.inr ⟨c / 2, by omega⟩ : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inr j : n ⊕ Fin (c + 1)) then
      V (.inr ⟨c / 2, by omega⟩) (.inr j) * W (.inr j) (.inl x) else 0) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h'
    · rw [hW _ _ (by simp [ordL] at h' ⊢; omega), Matrix.one_apply_ne (by simp), mul_zero]
    · rfl
  have h2 : (∑ y : n, if ordL (c + 1) (Sum.inr ⟨c / 2, by omega⟩ : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inl y : n ⊕ Fin (c + 1)) then
      V (.inr ⟨c / 2, by omega⟩) (.inl y) * W (.inl y) (.inl x) else 0) = V (.inr ⟨c / 2, by omega⟩) (.inl x) := by
    rw [Finset.sum_eq_single x]
    · rw [if_pos (by simp [ordL]; omega), hW _ _ le_rfl, Matrix.one_apply_eq, mul_one]
    · intro y _ hy
      rw [hW _ _ (by simp [ordL]), Matrix.one_apply_ne (by simpa using hy)]
      simp
    · simp
  rw [h1, h2] at h
  linear_combination h

theorem col_rel (hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → V r s = (1 : Matrix _ _ k) r s)
    (hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → W r s = (1 : Matrix _ _ k) r s) (hVW : V * W = 1)
    (hc : c % 2 = 1) (x : n) :
    V (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) + W (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) = 0 := by
  have h := congrFun (congrFun hVW (.inl x)) (.inr ⟨(c + 1) / 2, by omega⟩)
  rw [mul_apply_of_shape hV W, Matrix.one_apply_ne (by simp), Fintype.sum_sum_type] at h
  have h1 : (∑ j : Fin (c + 1), if ordL (c + 1) (Sum.inl x : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inr j : n ⊕ Fin (c + 1)) then
      V (.inl x) (.inr j) * W (.inr j) (.inr ⟨(c + 1) / 2, by omega⟩) else 0) = V (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) := by
    rw [Finset.sum_eq_single ⟨(c + 1) / 2, by omega⟩]
    · rw [if_pos (by simp [ordL]; omega), hW _ _ le_rfl, Matrix.one_apply_eq, mul_one]
    · intro j _ hj
      split_ifs with h'
      · rw [hW _ _ (by simp [ordL] at h' ⊢; omega), Matrix.one_apply_ne (by simpa using hj), mul_zero]
      · rfl
    · simp
  have h2 : (∑ y : n, if ordL (c + 1) (Sum.inl x : n ⊕ Fin (c + 1)) < ordL (c + 1) (Sum.inl y : n ⊕ Fin (c + 1)) then
      V (.inl x) (.inl y) * W (.inl y) (.inr ⟨(c + 1) / 2, by omega⟩) else 0) = 0 :=
    Finset.sum_eq_zero fun y _ => if_neg (by simp [ordL])
  rw [h1, h2] at h
  linear_combination h

theorem pair_right (hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → V r s = (1 : Matrix _ _ k) r s)
    (hc : c % 2 = 1) (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k) (x : n) :
    (stepPt x₁ e₁ * V) (.inr ⟨c / 2, by omega⟩) (.inl x) =
      stepPt x₁ e₁ (.inr ⟨c / 2, by omega⟩) (.inl x) + V (.inr ⟨c / 2, by omega⟩) (.inl x) := by
  rw [apply_mul_of_shape hV, Fintype.sum_sum_type]
  congr 1
  rw [Finset.sum_eq_zero fun y _ => if_neg (by simp [ordL]), zero_add, Finset.sum_eq_single ⟨c / 2, by omega⟩]
  · rw [if_pos (by simp [ordL]; omega), stepPt_rr_eq _ _ _ _ rfl, one_mul]
  · intro j _ hj
    split_ifs with h'
    · rw [stepPt_rr_lt _ _ _ _ ?_, zero_mul]
      simp [ordL] at h'
      have : j.val ≠ c / 2 := fun h => hj (Fin.ext h)
      simp
      omega
    · rfl
  · simp

theorem pair_left (hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → W r s = (1 : Matrix _ _ k) r s)
    (hc : c % 2 = 1) (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) (x : n) :
    (W * stepPt x₀ e₀) (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) =
      stepPt x₀ e₀ (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) + W (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) := by
  rw [mul_apply_of_shape hW, Fintype.sum_sum_type]
  congr 1
  rw [Finset.sum_eq_zero fun y _ => if_neg (by simp [ordL]), zero_add, Finset.sum_eq_single ⟨(c + 1) / 2, by omega⟩]
  · rw [if_pos (by simp [ordL]; omega), stepPt_rr_eq _ _ _ _ rfl, mul_one]
  · intro j _ hj
    split_ifs with h'
    · rw [stepPt_rr_lt _ _ _ _ ?_, mul_zero]
      simp [ordL] at h'
      have : j.val ≠ (c + 1) / 2 := fun h => hj (Fin.ext h)
      simp
      omega
    · rfl
  · simp

theorem row_left (hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → W r s = (1 : Matrix _ _ k) r s)
    (hc : c % 2 = 0) (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) (s : n₀) :
    (W * stepPt x₀ e₀) (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s) = stepPt x₀ e₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s) := by
  rw [mul_apply_of_shape hW, Fintype.sum_sum_type,
    Finset.sum_eq_zero fun y _ => if_neg (by simp [ordL]; omega), zero_add]
  rw [Finset.sum_eq_zero, add_zero]
  intro j _
  split_ifs with h'
  · rw [stepPt_rl_zero _ _ _ _ (by simp [ordL] at h'; omega), mul_zero]
  · rfl

theorem row_right (hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → V r s = (1 : Matrix _ _ k) r s)
    (hc : c % 2 = 0) (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k) (r : n₂) :
    (stepPt x₁ e₁ * V) (.inl r) (.inr ⟨c / 2, by omega⟩) = stepPt x₁ e₁ (.inl r) (.inr ⟨c / 2, by omega⟩) := by
  rw [apply_mul_of_shape hV, Fintype.sum_sum_type,
    Finset.sum_eq_zero fun y _ => if_neg (by simp [ordL]; omega), zero_add]
  rw [Finset.sum_eq_zero, add_zero]
  intro j _
  split_ifs with h'
  · rw [stepPt_lr_zero _ _ _ _ (by simp [ordL] at h'; omega), zero_mul]
  · rfl

end Rel

section GlobalTheory
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {m : ℕ}

theorem blk_mul_inr {β : Type} (P : Matrix n n k) (M : Matrix (n ⊕ Fin m) β k) (i : Fin m) (s : β) :
    ((fromBlocks P 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k) * M) (.inr i) s = M (.inr i) s := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_blk_inr {α : Type} (P : Matrix n n k) (M : Matrix α (n ⊕ Fin m) k) (r : α) (j : Fin m) :
    (M * (fromBlocks P 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k)) r (.inr j) = M r (.inr j) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem pair_blk {α β : Type} (K K' : Matrix n n k) (hK : K * K' = 1) (A : Matrix α (n ⊕ Fin m) k)
    (B : Matrix (n ⊕ Fin m) β k) (a : α) (b : β) :
    ∑ r, (A * (fromBlocks K 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k)) a (.inl r) *
      ((fromBlocks K' 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k) * B) (.inl r) b =
      ∑ r, A a (.inl r) * B (.inl r) b := by
  have hE : (fromBlocks K 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k) * fromBlocks K' 0 0 1 = 1 := by
    rw [fromBlocks_multiply]; simp [hK]
  have h : ((A * (fromBlocks K 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k)) *
      ((fromBlocks K' 0 0 1 : Matrix (n ⊕ Fin m) (n ⊕ Fin m) k) * B)) a b = (A * B) a b := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fromBlocks K 0 0 1), hE, Matrix.one_mul]
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type] at h
  simp only [mul_blk_inr, blk_mul_inr] at h
  exact add_right_cancel h

end GlobalTheory

theorem phase_step_inv : ∀ {k : Type} [Field k] {n₀ n n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂] {c : ℕ},
    ∀ v ∈ symN k n (c + 1), ∀ (κ : GL n k) (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k)
      (d₀ : Matrix (n ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k) (d₁ : Matrix (n₂ ⊕ Fin c) (n ⊕ Fin (c + 1)) k),
      d₀ = ((v * embX (c + 1) κ)⁻¹).val * stepPt x₀ e₀ → d₁ = stepPt x₁ e₁ * (v * embX (c + 1) κ).val →
      (ch d₀ + ch d₁ + (if Even (c + 1) then ∑ r : n, (∑ l : Fin c, if l.val = c / 2 then d₁ (.inr l) (.inl r) else 0) *
          d₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0) =
        ch (stepPt x₀ e₀) + ch (stepPt x₁ e₁) + (if Even (c + 1) then ∑ r : n,
          (∑ l : Fin c, if l.val = c / 2 then stepPt x₁ e₁ (.inr l) (.inl r) else 0) *
            stepPt x₀ e₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0)) ∧
      (Odd (c + 1) → (∀ s : n₀, d₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s) = stepPt x₀ e₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s)) ∧
        ∀ r : n₂, d₁ (.inl r) (.inr ⟨c / 2, by omega⟩) = stepPt x₁ e₁ (.inl r) (.inr ⟨c / 2, by omega⟩)) := by
  intro k _ n₀ n n₂ _ _ _ _ _ _ c v hv κ x₀ e₀ x₁ e₁ d₀ d₁ h₀ h₁
  have hV : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → v.val r s = (1 : Matrix (n ⊕ Fin (c + 1)) _ k) r s :=
    GlobalTheory.DiagVol.symN_le_unipSub hv
  have hW : ∀ r s, ordL (c + 1) s ≤ ordL (c + 1) r → (v⁻¹).val r s = (1 : Matrix (n ⊕ Fin (c + 1)) _ k) r s :=
    GlobalTheory.DiagVol.symN_le_unipSub (inv_mem hv)
  have hVW : v.val * (v⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hK : κ.val * (κ⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e₀' : d₀ = (fromBlocks (κ⁻¹).val 0 0 1 : Matrix (n ⊕ Fin (c + 1)) (n ⊕ Fin (c + 1)) k) * ((v⁻¹).val * stepPt x₀ e₀) := by
    rw [h₀, _root_.mul_inv_rev, Units.val_mul, ← map_inv, Matrix.mul_assoc]; rfl
  have e₁' : d₁ = (stepPt x₁ e₁ * v.val) * (fromBlocks κ.val 0 0 1 : Matrix (n ⊕ Fin (c + 1)) (n ⊕ Fin (c + 1)) k) := by
    rw [h₁, Units.val_mul, ← Matrix.mul_assoc]; rfl
  have hch₀ : ch d₀ = ch ((v⁻¹).val * stepPt x₀ e₀) := by
    rw [e₀']; unfold ch; simp only [blk_mul_inr]
  have hch₁ : ch d₁ = ch (stepPt x₁ e₁ * v.val) := by
    rw [e₁']; unfold ch; simp only [mul_blk_inr]
  rw [hch₀, hch₁, ch_shape_mul hW, ch_mul_shape hV]
  have hrel := fun l => simple_rel hV hW hVW l
  rcases Nat.even_or_odd (c + 1) with hc | hc
  · have hc' : c % 2 = 1 := by rcases hc with ⟨r, hr⟩; omega
    refine ⟨?_, fun h => absurd h (Nat.not_odd_iff_even.mpr hc)⟩
    rw [if_pos hc, if_pos hc]
    have hs0 : (⟨c / 2, by omega⟩ : Fin (c + 1)).succ = ⟨(c + 1) / 2, by omega⟩ := Fin.ext (by simp; omega)
    have hs1 : (⟨c / 2, by omega⟩ : Fin c).succ = ⟨(c + 1) / 2, by omega⟩ := Fin.ext (by simp; omega)
    have hcs : (⟨c / 2, by omega⟩ : Fin c).castSucc = ⟨c / 2, by omega⟩ := rfl
    have f0 : (∑ i : Fin (c + 1), if 2 * i.val + 1 = c then
        ∑ x, (v⁻¹).val (.inr i) (.inl x) * stepPt x₀ e₀ (.inl x) (.inr i.succ) else 0) =
        ∑ x, (v⁻¹).val (.inr ⟨c / 2, by omega⟩) (.inl x) * stepPt x₀ e₀ (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) := by
      rw [Finset.sum_eq_single ⟨c / 2, by omega⟩, if_pos (by simp; omega), hs0]
      · intro i _ hi; rw [if_neg]; intro h; exact hi (Fin.ext (by simp; omega))
      · simp
    have f1 : (∑ l : Fin c, if 2 * l.val + 1 = c then
        ∑ x, stepPt x₁ e₁ (.inr l) (.inl x) * v.val (.inl x) (.inr l.succ) else 0) =
        ∑ x, stepPt x₁ e₁ (.inr ⟨c / 2, by omega⟩) (.inl x) * v.val (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) := by
      rw [Finset.sum_eq_single ⟨c / 2, by omega⟩, if_pos (by simp; omega), hs1]
      · intro i _ hi; rw [if_neg]; intro h; exact hi (Fin.ext (by simp; omega))
      · simp
    have hS : ∑ l : Fin c, v.val (.inr l.castSucc) (.inr l.succ) + ∑ l : Fin c, (v⁻¹).val (.inr l.castSucc) (.inr l.succ) +
        ∑ x, v.val (.inr ⟨c / 2, by omega⟩) (.inl x) * (v⁻¹).val (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) = 0 := by
      have h := Finset.sum_eq_zero (s := Finset.univ) fun l _ => hrel l
      have f2 : (∑ l : Fin c, if 2 * l.val + 1 = c then
          ∑ x, v.val (.inr l.castSucc) (.inl x) * (v⁻¹).val (.inl x) (.inr l.succ) else 0) =
          ∑ x, v.val (.inr ⟨c / 2, by omega⟩) (.inl x) * (v⁻¹).val (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) := by
        rw [Finset.sum_eq_single ⟨c / 2, by omega⟩, if_pos (by simp; omega), hs1, hcs]
        · intro i _ hi; rw [if_neg]; intro h; exact hi (Fin.ext (by simp; omega))
        · simp
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, f2] at h
      exact h
    have hp : ∀ (D₁ : Matrix (n₂ ⊕ Fin c) (n ⊕ Fin (c + 1)) k) r,
        (∑ l : Fin c, if l.val = c / 2 then D₁ (.inr l) (.inl r) else 0) = D₁ (.inr ⟨c / 2, by omega⟩) (.inl r) := by
      intro D₁ r
      rw [Finset.sum_eq_single ⟨c / 2, by omega⟩, if_pos rfl]
      · intro i _ hi; rw [if_neg]; intro h; exact hi (Fin.ext h)
      · simp
    simp only [hp]
    rw [e₀', e₁', pair_blk _ _ hK, f0, f1]
    simp only [pair_right hV hc' x₁ e₁, pair_left hW hc' x₀ e₀]
    have hl : ∀ x, (v⁻¹).val (.inr ⟨c / 2, by omega⟩) (.inl x) = -v.val (.inr ⟨c / 2, by omega⟩) (.inl x) :=
      fun x => eq_neg_of_add_eq_zero_right (row_rel hV hW hVW hc' x)
    have hb : ∀ x, (v⁻¹).val (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) = -v.val (.inl x) (.inr ⟨(c + 1) / 2, by omega⟩) :=
      fun x => eq_neg_of_add_eq_zero_right (col_rel hV hW hVW hc' x)
    simp only [hl, hb] at hS ⊢
    simp only [add_mul, mul_add, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib] at hS ⊢
    linear_combination hS
  · have hc' : c % 2 = 0 := by rcases hc with ⟨r, hr⟩; omega
    have hne : ¬ Even (c + 1) := Nat.not_even_iff_odd.mpr hc
    refine ⟨?_, fun _ => ⟨fun s => ?_, fun r => ?_⟩⟩
    · rw [if_neg hne, if_neg hne]
      have z0 : ∀ i : Fin (c + 1), ¬ (2 * i.val + 1 = c) := fun i => by omega
      have z1 : ∀ i : Fin c, ¬ (2 * i.val + 1 = c) := fun i => by omega
      simp only [z0, z1, if_false, Finset.sum_const_zero, add_zero]
      have hS : ∑ l : Fin c, v.val (.inr l.castSucc) (.inr l.succ) + ∑ l : Fin c, (v⁻¹).val (.inr l.castSucc) (.inr l.succ) = 0 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero fun l _ => by simpa [z1 l] using hrel l
      linear_combination hS
    · rw [e₀', blk_mul_inr, row_left hW hc']
    · rw [e₁', mul_blk_inr, row_right hV hc']

end GlobalTheory.PhaseStep
