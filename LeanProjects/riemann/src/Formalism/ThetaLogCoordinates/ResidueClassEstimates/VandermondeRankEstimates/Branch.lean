import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementT

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

namespace Branch

def ff (j : ℕ) (x : ℝ) : ℝ := ∏ k ∈ range j, (x - k)

lemma ff_zero (x : ℝ) : ff 0 x = 1 := by simp [ff]

lemma ff_diff (j : ℕ) (x : ℝ) : ff (j + 1) (x + 1) - ff (j + 1) x = ((j : ℝ) + 1) * ff j x := by
  have h1 : ff (j + 1) (x + 1) = (x + 1) * ff j x := by
    unfold ff
    rw [Finset.prod_range_succ']
    rw [mul_comm]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun k _ => ?_
      push_cast; ring
  have h2 : ff (j + 1) x = ff j x * (x - j) := by
    unfold ff
    rw [Finset.prod_range_succ]
  rw [h1, h2]; ring

lemma sum_Ico_int_sub (F : ℤ → ℝ) (a b : ℤ) (h : a ≤ b) :
    ∑ x ∈ Ico a b, (F (x + 1) - F x) = F b - F a := by
  induction b, h using Int.leInduction with
  | base => simp
  | succ b hb ih =>
    rw [← Finset.insert_Ico_right_eq_Ico_add_one hb, Finset.sum_insert Finset.right_notMem_Ico, ih]
    ring

lemma sum_ff (j : ℕ) (c : ℝ) (a b : ℤ) (h : a ≤ b) :
    ((j : ℝ) + 1) * ∑ x ∈ Icc a b, ff j (c - (x : ℝ)) =
      ff (j + 1) (c + 1 - (a : ℝ)) - ff (j + 1) (c - (b : ℝ)) := by
  have := sum_Ico_int_sub (fun x => - ff (j + 1) (c + 1 - (x : ℝ))) a (b + 1) (by omega)
  rw [Finset.Ico_add_one_right_eq_Icc] at this
  rw [Finset.mul_sum]
  have e : ∀ x ∈ Icc a b, ((j : ℝ) + 1) * ff j (c - (x : ℝ)) =
      - ff (j + 1) (c + 1 - ((x + 1 : ℤ) : ℝ)) - - ff (j + 1) (c + 1 - (x : ℝ)) := by
    intro x _
    rw [← ff_diff]
    push_cast
    have e1 : c + 1 - ((x : ℝ) + 1) = c - x := by ring
    have e2 : c + 1 - (x : ℝ) = c - x + 1 := by ring
    rw [e1, e2]; ring
  rw [Finset.sum_congr rfl e, this]
  push_cast
  have e1 : c + 1 - ((b : ℝ) + 1) = c - b := by ring
  rw [e1]; ring

lemma det_vandermonde_eq_ff {n : ℕ} (v : Fin n → ℝ) :
    (Matrix.vandermonde v).det = (Matrix.of fun i j : Fin n => ff j (v i)).det := by
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v (fun j => descPochhammer ℝ j)
    (fun j => descPochhammer_natDegree ℝ j) (fun j => monic_descPochhammer ℝ j)]
  congr 1
  ext i j
  simp only [Matrix.of_apply, descPochhammer_eval_eq_prod_range, ff]

lemma sum_det {n : ℕ} (S : Fin n → Finset ℤ) (g : Fin n → ℤ → Fin n → ℝ) :
    ∑ r ∈ Fintype.piFinset S, (Matrix.of fun i j : Fin n => g i (r i) j).det =
      (Matrix.of fun i j : Fin n => ∑ x ∈ S i, g i x j).det := by
  have := (Matrix.detRowAlternating (n := Fin n) (R := ℝ)).toMultilinearMap.map_sum_finset g S
  have e : (fun i => ∑ x ∈ S i, g i x) = (Matrix.of fun i j : Fin n => ∑ x ∈ S i, g i x j) := by
    ext i j
    simp [Finset.sum_apply]
  rw [e] at this
  exact this.symm

lemma det_diff {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (h : ∀ i, M i 0 = 1) :
    M.det = (Matrix.of fun i j : Fin n => M i.succ j.succ - M i.castSucc j.succ).det := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j => Fin.cases (M 0 j) (fun i' => M i'.succ j - M i'.castSucc j) i
  have h1 : M.det = B.det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1) (fun j => ?_) (fun i j => ?_)
    · simp [B]
    · simp [B]
  rw [h1, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h2 : ∀ i : Fin n, B i.succ 0 = 0 := by
    intro i; simp [B, h]
  have h3 : B 0 0 = 1 := by simp [B, h]
  simp only [h2, h3, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  congr 1

def W (n : ℕ) (u : ℕ → ℝ) : ℝ := ∏ j ∈ range n, ∏ i ∈ range j, (u j - u i)

lemma det_vandermonde_eq_vandermondeProd (n : ℕ) (u : ℕ → ℝ) :
    (Matrix.vandermonde fun i : Fin n => u i).det = W n u := by
  rw [Matrix.det_vandermonde, W,
    Finset.prod_comm' (s' := fun j : Fin n => Iio j) (t' := (univ : Finset (Fin n)))
      (by intro x y; simp),
    ← Fin.prod_univ_eq_prod_range (fun j => ∏ i ∈ range j, (u j - u i)) n]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.prod_map]
  rfl

lemma extW_val {n : ℕ} (la : Fin n → ℤ) (i : Fin n) : extW la i.val = la i := by
  simp [extW]

lemma weylDim_eq (n : ℕ) (la : ℕ → ℤ) :
    weylDim n la = W n (fun m => (m : ℝ) - (la m : ℝ)) / W n (fun m => (m : ℝ)) := by
  unfold weylDim W
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  push_cast; ring

lemma W_id_ne_zero (n : ℕ) : W n (fun m => (m : ℝ)) ≠ 0 := by
  unfold W
  refine Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun i hi => ?_
  have : (i : ℝ) < j := by exact_mod_cast Finset.mem_range.1 hi
  exact sub_ne_zero.2 this.ne'

lemma W_id_succ (n : ℕ) :
    W (n + 1) (fun m => (m : ℝ)) = W n (fun m => (m : ℝ)) * ∏ j : Fin n, ((j : ℝ) + 1) := by
  unfold W
  rw [Finset.prod_range_succ, Fin.prod_univ_eq_prod_range (fun j => (j : ℝ) + 1) n,
    ← Finset.prod_range_reflect (fun j => (j : ℝ) + 1) n]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.1 hi
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

lemma core {n : ℕ} (mu : Fin (n + 1) → ℤ) (h : ∀ i : Fin n, mu i.succ ≤ mu i.castSucc) :
    (∏ j : Fin n, ((j : ℝ) + 1)) *
      ∑ la ∈ Fintype.piFinset (fun i : Fin n => Icc (mu i.succ) (mu i.castSucc)),
        (Matrix.vandermonde fun i : Fin n => (i : ℝ) - (la i : ℝ)).det =
      (Matrix.vandermonde fun i : Fin (n + 1) => (i : ℝ) - (mu i : ℝ)).det := by
  simp_rw [det_vandermonde_eq_ff]
  rw [sum_det (fun i : Fin n => Icc (mu i.succ) (mu i.castSucc)) (fun i x j => ff j ((i : ℝ) - (x : ℝ))),
    ← Matrix.det_mul_row, det_diff _ (by intro i; simp [ff_zero])]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [sum_ff _ _ _ _ (h i)]
  simp

lemma finsum_prop_eq_sum {α : Type*} (p : α → Prop) (s : Finset α) (f : α → ℝ) (h : ∀ a, p a ↔ a ∈ s) :
    ∑ᶠ (a : α) (_ : p a), f a = ∑ a ∈ s, f a := by
  rw [← finsum_mem_coe_finset]
  refine finsum_congr fun a => ?_
  have e : p a = (a ∈ (s : Set α)) := propext (by rw [Finset.mem_coe]; exact h a)
  rw [e]

lemma interl_iff {n : ℕ} (la : Fin n → ℤ) (mu : Fin (n + 1) → ℤ) :
    Interl n (extW la) (extW mu) ↔
      la ∈ Fintype.piFinset (fun i : Fin n => Icc (mu i.succ) (mu i.castSucc)) := by
  rw [Fintype.mem_piFinset]
  constructor
  · intro h i
    have := h i.val i.isLt
    rw [extW_val] at this
    have e1 : extW mu i.val = mu i.castSucc := extW_val mu i.castSucc
    have e2 : extW mu (i.val + 1) = mu i.succ := extW_val mu i.succ
    rw [e1, e2] at this
    exact Finset.mem_Icc.2 ⟨this.2, this.1⟩
  · intro h l hl
    have := Finset.mem_Icc.1 (h ⟨l, hl⟩)
    have e0 : extW la l = la ⟨l, hl⟩ := extW_val la ⟨l, hl⟩
    have e1 : extW mu l = mu (Fin.castSucc ⟨l, hl⟩) := extW_val mu (Fin.castSucc ⟨l, hl⟩)
    have e2 : extW mu (l + 1) = mu (Fin.succ ⟨l, hl⟩) := extW_val mu (Fin.succ ⟨l, hl⟩)
    rw [e0, e1, e2]
    exact ⟨this.2, this.1⟩

lemma W_extW {n : ℕ} (la : Fin n → ℤ) :
    W n (fun m => (m : ℝ) - (extW la m : ℝ)) = (Matrix.vandermonde fun i : Fin n => (i : ℝ) - (la i : ℝ)).det := by
  rw [← det_vandermonde_eq_vandermondeProd]
  simp only [extW_val]

end Branch

open Branch in

theorem branchingDimensionFormula : BranchDim := by
  intro n mu hmu
  have h : ∀ i : Fin n, mu i.succ ≤ mu i.castSucc := by
    intro i
    have := hmu i.val (by have := i.isLt; omega)
    have e1 : extW mu i.val = mu i.castSucc := extW_val mu i.castSucc
    have e2 : extW mu (i.val + 1) = mu i.succ := extW_val mu i.succ
    rwa [e1, e2] at this
  rw [finsum_prop_eq_sum _ _ _ (fun la => interl_iff la mu)]
  simp_rw [weylDim_eq, W_extW]
  rw [← Finset.sum_div, ← core mu h, W_id_succ]
  have h0 := W_id_ne_zero n
  have h1 : (∏ j : Fin n, ((j : ℝ) + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => by positivity
  field_simp

end Formalism.InvariantFactorPaths.BranchingDimensions
