import Mathlib
import GroundTheory.AutomorphicForms.FiniteBruhat
import GroundTheory.AutomorphicForms.Iwasawa

namespace GroundTheory.Automorphic

namespace Whittaker

open Matrix DoubleCoset

variable {F : Type*} [Field F] {n : ℕ}

section Rank

def rowsFrom (i : Fin n) : Matrix (Fin n) (Fin n) F := diagonal fun r => if i ≤ r then 1 else 0

def colsTo (j : Fin n) : Matrix (Fin n) (Fin n) F := diagonal fun c => if c ≤ j then 1 else 0

noncomputable def llRank (i j : Fin n) (g : GL (Fin n) F) : ℕ :=
  (rowsFrom i * (g : Matrix (Fin n) (Fin n) F) * colsTo j).rank

theorem le_rank_iff_exists_det_ne_zero {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m F) (k : ℕ) :
    k ≤ M.rank ↔ ∃ (A : Matrix (Fin k) m F) (B : Matrix m (Fin k) F), (A * M * B).det ≠ 0 := by
  constructor
  · intro hk
    obtain ⟨V, U, e, -, -, hVU⟩ := exists_rank_normal_form M
    let f : Fin k → m := fun a => e.symm (Sum.inl (Fin.castLE hk a))
    refine ⟨V.submatrix f id, U.submatrix id f, ?_⟩
    have h1 : V.submatrix f id * M * U.submatrix id f = (V * M * U).submatrix f f := by
      rw [submatrix_mul _ _ f id f Function.bijective_id,
        submatrix_mul _ _ f id id Function.bijective_id, submatrix_id_id]
    have h2 : (V * M * U).submatrix f f = 1 := by
      rw [hVU, submatrix_submatrix]
      ext a b
      simp [f, Matrix.one_apply, Fin.castLE_inj]
    rw [h1, h2, det_one]
    exact one_ne_zero
  · rintro ⟨A, B, hAB⟩
    have h := rank_of_det_ne_zero hAB
    rw [Fintype.card_fin] at h
    calc k = (A * M * B).rank := h.symm
      _ ≤ (A * M).rank := rank_mul_le_left _ _
      _ ≤ M.rank := rank_mul_le_right _ _

theorem llRank_le (i j : Fin n) (g : GL (Fin n) F) : llRank i j g ≤ n := by
  have := rank_le_card_width (rowsFrom i * (g : Matrix (Fin n) (Fin n) F) * colsTo j)
  rwa [Fintype.card_fin] at this

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]

theorem isOpen_setOf_le_llRank (i j : Fin n) (k : ℕ) :
    IsOpen {g : GL (Fin n) F | k ≤ llRank i j g} := by
  have e : {g : GL (Fin n) F | k ≤ llRank i j g} =
      ⋃ (A : Matrix (Fin k) (Fin n) F) (B : Matrix (Fin n) (Fin k) F),
        {g | (A * (rowsFrom i * (g : Matrix (Fin n) (Fin n) F) * colsTo j) * B).det ≠ 0} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, llRank]
    exact le_rank_iff_exists_det_ne_zero _ k
  rw [e]
  refine isOpen_iUnion fun A => isOpen_iUnion fun B => ?_
  have hc : Continuous fun g : GL (Fin n) F =>
      (A * (rowsFrom i * (g : Matrix (Fin n) (Fin n) F) * colsTo j) * B).det :=
    ((continuous_const.matrix_mul ((continuous_const.matrix_mul Units.continuous_val).matrix_mul
      continuous_const)).matrix_mul continuous_const).matrix_det
  exact isOpen_compl_singleton.preimage hc

theorem isOpen_setOf_forall_le_llRank (r : Fin n → Fin n → ℕ) :
    IsOpen {g : GL (Fin n) F | ∀ i j, r i j ≤ llRank i j g} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_setOf_le_llRank i j (r i j)

theorem isClosed_setOf_forall_llRank_le (r : Fin n → Fin n → ℕ) :
    IsClosed {g : GL (Fin n) F | ∀ i j, llRank i j g ≤ r i j} := by
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  have : {g : GL (Fin n) F | llRank i j g ≤ r i j} = {g | r i j + 1 ≤ llRank i j g}ᶜ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    omega
  rw [this]
  exact (isOpen_setOf_le_llRank i j (r i j + 1)).isClosed_compl

end Topology

theorem rowsFrom_mul_self (i : Fin n) :
    rowsFrom i * rowsFrom i = (rowsFrom i : Matrix (Fin n) (Fin n) F) := by
  simp only [rowsFrom, diagonal_mul_diagonal]
  congr 1
  funext r
  split_ifs <;> simp

theorem colsTo_mul_self (j : Fin n) :
    colsTo j * colsTo j = (colsTo j : Matrix (Fin n) (Fin n) F) := by
  simp only [colsTo, diagonal_mul_diagonal]
  congr 1
  funext r
  split_ifs <;> simp

theorem rowsFrom_mul_mul_rowsFrom {b : Matrix (Fin n) (Fin n) F} (hb : b.IsUpperTriangular)
    (i : Fin n) : rowsFrom i * b * rowsFrom i = rowsFrom i * b := by
  ext r c
  simp only [rowsFrom, diagonal_mul, mul_diagonal]
  by_cases h1 : i ≤ r <;> by_cases h2 : i ≤ c
  · simp [h1, h2]
  · rw [hb (show id c < id r from lt_of_lt_of_le (not_le.1 h2) h1)]
    simp
  · simp [h1]
  · simp [h1]

theorem colsTo_mul_mul_colsTo {b : Matrix (Fin n) (Fin n) F} (hb : b.IsUpperTriangular)
    (j : Fin n) : colsTo j * b * colsTo j = b * colsTo j := by
  ext r c
  simp only [colsTo, diagonal_mul, mul_diagonal]
  by_cases h1 : r ≤ j <;> by_cases h2 : c ≤ j
  · simp [h1, h2]
  · simp [h2]
  · rw [hb (show id c < id r from lt_of_le_of_lt h2 (not_le.1 h1))]
    simp
  · simp [h2]

theorem isUnit_det_of_isUpperTriangular {X : Matrix (Fin n) (Fin n) F} (hX : X.IsUpperTriangular)
    (hd : ∀ r, X r r ≠ 0) : IsUnit X.det := by
  rw [det_of_isUpperTriangular hX, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun r _ => hd r

theorem llRank_mul_mul {b b' : GL (Fin n) F} (hb : b ∈ borel n F) (hb' : b' ∈ borel n F)
    (i j : Fin n) (g : GL (Fin n) F) : llRank i j (b * g * b') = llRank i j g := by
  classical
  have hbu : (b : Matrix (Fin n) (Fin n) F).IsUpperTriangular := hb
  have hbu' : (b' : Matrix (Fin n) (Fin n) F).IsUpperTriangular := hb'
  set P : Matrix (Fin n) (Fin n) F := rowsFrom i with hP
  set E : Matrix (Fin n) (Fin n) F := colsTo j with hE
  set X : Matrix (Fin n) (Fin n) F := P * (b : Matrix (Fin n) (Fin n) F) + (1 - P) with hXdef
  set Y : Matrix (Fin n) (Fin n) F := (b' : Matrix (Fin n) (Fin n) F) * E + (1 - E) with hYdef
  have hXP : X * P = P * (b : Matrix (Fin n) (Fin n) F) := by
    rw [hXdef, add_mul, sub_mul, one_mul, hP, rowsFrom_mul_self, sub_self, add_zero,
      rowsFrom_mul_mul_rowsFrom hbu]
  have hEY : E * Y = (b' : Matrix (Fin n) (Fin n) F) * E := by
    rw [hYdef, mul_add, mul_sub, mul_one, hE, colsTo_mul_self, sub_self, add_zero,
      ← mul_assoc, colsTo_mul_mul_colsTo hbu']
  have key : P * ((b * g * b' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * E =
      X * (P * (g : Matrix (Fin n) (Fin n) F) * E) * Y := by
    simp only [Units.val_mul]
    calc P * ((b : Matrix (Fin n) (Fin n) F) * g * b') * E
        = (P * b) * g * (b' * E) := by simp only [mul_assoc]
      _ = (X * P) * g * (E * Y) := by rw [hXP, hEY]
      _ = X * (P * g * E) * Y := by simp only [mul_assoc]
  have hXu : X.IsUpperTriangular :=
    ((blockTriangular_diagonal _).mul hbu).add (blockTriangular_one.sub (blockTriangular_diagonal _))
  have hYu : Y.IsUpperTriangular :=
    (hbu'.mul (blockTriangular_diagonal _)).add (blockTriangular_one.sub (blockTriangular_diagonal _))
  have hX : IsUnit X.det := by
    refine isUnit_det_of_isUpperTriangular hXu fun r => ?_
    rw [hXdef, hP, rowsFrom, Matrix.add_apply, Matrix.sub_apply, diagonal_mul, one_apply_eq,
      diagonal_apply_eq]
    split_ifs
    · simpa using borel_diag_ne_zero hb r
    · simp
  have hY : IsUnit Y.det := by
    refine isUnit_det_of_isUpperTriangular hYu fun r => ?_
    rw [hYdef, hE, colsTo, Matrix.add_apply, Matrix.sub_apply, mul_diagonal, one_apply_eq,
      diagonal_apply_eq]
    split_ifs
    · simpa using borel_diag_ne_zero hb' r
    · simp
  unfold llRank
  rw [← hP, ← hE, key, rank_mul_eq_left_of_isUnit_det Y _ hY,
    rank_mul_eq_right_of_isUnit_det X _ hX]

theorem llRank_permGL (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    llRank i j (permGL F w) = (Finset.univ.filter fun r : Fin n => i ≤ r ∧ w⁻¹ r ≤ j).card := by
  classical
  have hW : IsUnit ((permGL F w⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  unfold llRank
  rw [← rank_mul_eq_left_of_isUnit_det _ _ hW]
  have e : rowsFrom i * (permGL F w : Matrix (Fin n) (Fin n) F) * colsTo j *
      (permGL F w⁻¹ : Matrix (Fin n) (Fin n) F) =
      diagonal fun r => if i ≤ r ∧ w⁻¹ r ≤ j then (1 : F) else 0 := by
    ext r c
    rw [mul_permGL_apply]
    simp only [rowsFrom, colsTo]
    rw [mul_diagonal, diagonal_mul, permGL_apply, diagonal_apply]
    have hwc : w (w⁻¹ c) = c := by rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    rw [hwc]
    by_cases hrc : r = c
    · subst hrc
      by_cases h1 : i ≤ r <;> simp [h1]
    · simp [hrc]
  rw [e, rank_diagonal, Fintype.card_subtype]
  congr 1
  ext r
  simp

theorem card_filter_le_eq (w : Equiv.Perm (Fin n)) (r j : Fin n) :
    (Finset.univ.filter fun x : Fin n => r ≤ x ∧ w⁻¹ x ≤ j).card =
      (if w⁻¹ r ≤ j then 1 else 0) + (Finset.univ.filter fun x : Fin n => r < x ∧ w⁻¹ x ≤ j).card := by
  classical
  have hsplit : (Finset.univ.filter fun x : Fin n => r ≤ x ∧ w⁻¹ x ≤ j) =
      (Finset.univ.filter fun x : Fin n => x = r ∧ w⁻¹ x ≤ j) ∪
        (Finset.univ.filter fun x : Fin n => r < x ∧ w⁻¹ x ≤ j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h | h
      · exact Or.inl ⟨h.symm, h2⟩
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨rfl, h⟩ | ⟨h1, h2⟩)
      · exact ⟨le_rfl, h⟩
      · exact ⟨h1.le, h2⟩
  have hdisj : Disjoint (Finset.univ.filter fun x : Fin n => x = r ∧ w⁻¹ x ≤ j)
      (Finset.univ.filter fun x : Fin n => r < x ∧ w⁻¹ x ≤ j) := by
    rw [Finset.disjoint_filter]
    rintro x - ⟨rfl, -⟩ ⟨h, -⟩
    exact lt_irrefl _ h
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  congr 1
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, -⟩
      rfl
    · rintro rfl
      exact ⟨rfl, h⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨rfl, hx⟩
    exact h hx

theorem card_filter_lt_eq (w : Equiv.Perm (Fin n)) (r j : Fin n) :
    (Finset.univ.filter fun x : Fin n => r < x ∧ w⁻¹ x ≤ j).card =
      if h : r.val + 1 < n then llRank ⟨r.val + 1, h⟩ j (permGL F w) else 0 := by
  split_ifs with h
  · rw [llRank_permGL]
    congr 1
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨hx, -⟩
    rw [Fin.lt_def] at hx
    have := x.isLt
    omega

theorem perm_eq_of_llRank {w w' : Equiv.Perm (Fin n)}
    (h : ∀ i j, llRank i j (permGL F w) = llRank i j (permGL F w')) : w = w' := by
  have key : ∀ r j, (w⁻¹ r ≤ j ↔ w'⁻¹ r ≤ j) := by
    intro r j
    have hA : (Finset.univ.filter fun x : Fin n => r ≤ x ∧ w⁻¹ x ≤ j).card =
        (Finset.univ.filter fun x : Fin n => r ≤ x ∧ w'⁻¹ x ≤ j).card := by
      rw [← llRank_permGL (F := F), ← llRank_permGL (F := F), h]
    have hB : (Finset.univ.filter fun x : Fin n => r < x ∧ w⁻¹ x ≤ j).card =
        (Finset.univ.filter fun x : Fin n => r < x ∧ w'⁻¹ x ≤ j).card := by
      rw [card_filter_lt_eq (F := F), card_filter_lt_eq (F := F)]
      split_ifs with hr
      · exact h _ _
      · rfl
    have e1 := card_filter_le_eq w r j
    rw [hA, card_filter_le_eq w' r j, hB] at e1
    constructor
    · intro hw
      by_contra hw'
      rw [if_pos hw, if_neg hw'] at e1
      omega
    · intro hw'
      by_contra hw
      rw [if_pos hw', if_neg hw] at e1
      omega
  have hinv : w⁻¹ = w'⁻¹ := by
    ext r
    exact congrArg Fin.val (le_antisymm ((key r (w'⁻¹ r)).2 le_rfl) ((key r (w⁻¹ r)).1 le_rfl))
  exact inv_injective hinv

end Rank

section Cell

noncomputable def bruhatCell (g : GL (Fin n) F) : Equiv.Perm (Fin n) :=
  (exists_mem_doubleCoset_permGL g).choose

theorem mem_doubleCoset_bruhatCell (g : GL (Fin n) F) :
    g ∈ doubleCoset (permGL F (bruhatCell g)) (borel n F) (borel n F) :=
  (exists_mem_doubleCoset_permGL g).choose_spec

theorem bruhatCell_eq_iff {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)} :
    bruhatCell g = w ↔ g ∈ doubleCoset (permGL F w) (borel n F) (borel n F) := by
  constructor
  · rintro rfl
    exact mem_doubleCoset_bruhatCell g
  · intro h
    exact doubleCoset_permGL_injective (mem_doubleCoset_bruhatCell g) h

theorem bruhatCell_permGL (w : Equiv.Perm (Fin n)) : bruhatCell (permGL F w) = w :=
  bruhatCell_eq_iff.2 (mem_doubleCoset_self _ _ _)

theorem bruhatCell_mul_mul {a b : GL (Fin n) F} (ha : a ∈ borel n F) (hb : b ∈ borel n F)
    (g : GL (Fin n) F) : bruhatCell (a * g * b) = bruhatCell g := by
  rw [bruhatCell_eq_iff]
  obtain ⟨x, hx, y, hy, hg⟩ := mem_doubleCoset.1 (mem_doubleCoset_bruhatCell g)
  refine mem_doubleCoset.2 ⟨a * x, (borel n F).mul_mem ha hx, y * b, (borel n F).mul_mem hy hb, ?_⟩
  calc a * g * b = a * (x * permGL F (bruhatCell g) * y) * b := by rw [← hg]
    _ = a * x * permGL F (bruhatCell g) * (y * b) := by group

theorem llRank_eq_llRank_bruhatCell (i j : Fin n) (g : GL (Fin n) F) :
    llRank i j g = llRank i j (permGL F (bruhatCell g)) := by
  obtain ⟨x, hx, y, hy, hg⟩ := mem_doubleCoset.1 (mem_doubleCoset_bruhatCell g)
  conv_lhs => rw [hg]
  exact llRank_mul_mul hx hy i j _

theorem bruhatCell_eq_iff_llRank {g g' : GL (Fin n) F} :
    bruhatCell g = bruhatCell g' ↔ ∀ i j, llRank i j g = llRank i j g' := by
  constructor
  · intro h i j
    rw [llRank_eq_llRank_bruhatCell i j g, llRank_eq_llRank_bruhatCell i j g', h]
  · intro h
    apply perm_eq_of_llRank (F := F)
    intro i j
    rw [← llRank_eq_llRank_bruhatCell, ← llRank_eq_llRank_bruhatCell]
    exact h i j

end Cell

section NormalForm

theorem unipotent_le_borel : Iwasawa.unipotent F n ≤ borel n F := fun _ hg => hg.1

theorem diagGL_mem_borel (t : Fin n → Fˣ) : Iwasawa.diagGL F n t ∈ borel n F := by
  show ((Iwasawa.diagGL F n t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsUpperTriangular
  rw [Iwasawa.coe_diagGL]
  exact blockTriangular_diagonal _

noncomputable def borelDiag {b : GL (Fin n) F} (hb : b ∈ borel n F) : Fin n → Fˣ :=
  fun i => Units.mk0 _ (borel_diag_ne_zero hb i)

theorem mul_inv_borelDiag_mem {b : GL (Fin n) F} (hb : b ∈ borel n F) :
    b * (Iwasawa.diagGL F n (borelDiag hb))⁻¹ ∈ Iwasawa.unipotent F n := by
  have hbu : (b : Matrix (Fin n) (Fin n) F).IsUpperTriangular := hb
  rw [Iwasawa.mem_unipotent F n, ← map_inv, Units.val_mul, Iwasawa.coe_diagGL]
  refine ⟨hbu.mul (blockTriangular_diagonal _), fun i => ?_⟩
  rw [mul_diagonal]
  simp only [borelDiag, Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_mk0]
  exact mul_inv_cancel₀ (borel_diag_ne_zero hb i)

theorem inv_borelDiag_mul_mem {b : GL (Fin n) F} (hb : b ∈ borel n F) :
    (Iwasawa.diagGL F n (borelDiag hb))⁻¹ * b ∈ Iwasawa.unipotent F n := by
  have hbu : (b : Matrix (Fin n) (Fin n) F).IsUpperTriangular := hb
  rw [Iwasawa.mem_unipotent F n, ← map_inv, Units.val_mul, Iwasawa.coe_diagGL]
  refine ⟨(blockTriangular_diagonal _).mul hbu, fun i => ?_⟩
  rw [diagonal_mul]
  simp only [borelDiag, Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_mk0]
  exact inv_mul_cancel₀ (borel_diag_ne_zero hb i)

theorem permGL_mul_diagGL (w : Equiv.Perm (Fin n)) (d : Fin n → Fˣ) :
    permGL F w * Iwasawa.diagGL F n d = Iwasawa.diagGL F n (fun r => d (w⁻¹ r)) * permGL F w := by
  ext r c
  rw [Units.val_mul, Units.val_mul, Iwasawa.coe_diagGL, Iwasawa.coe_diagGL, permGL_mul_apply,
    diagonal_apply, diagonal_mul, permGL_apply]
  by_cases h : r = w c
  · have : w⁻¹ r = c := Equiv.Perm.inv_eq_iff_eq.2 h
    rw [if_pos this, if_pos h, mul_one]
  · have : w⁻¹ r ≠ c := fun e => h (Equiv.Perm.inv_eq_iff_eq.1 e)
    rw [if_neg this, if_neg h, mul_zero]

theorem mem_doubleCoset_iff_normalForm {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)} :
    g ∈ doubleCoset (permGL F w) (borel n F) (borel n F) ↔
      ∃ u ∈ Iwasawa.unipotent F n, ∃ t : Fin n → Fˣ, ∃ v ∈ Iwasawa.unipotent F n,
        g = u * Iwasawa.diagGL F n t * permGL F w * v := by
  constructor
  · intro h
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_doubleCoset.1 h
    refine ⟨x * (Iwasawa.diagGL F n (borelDiag hx))⁻¹, mul_inv_borelDiag_mem hx,
      borelDiag hx * (fun r => borelDiag hy (w⁻¹ r)),
      (Iwasawa.diagGL F n (borelDiag hy))⁻¹ * y, inv_borelDiag_mul_mem hy, ?_⟩
    rw [map_mul]
    have e := permGL_mul_diagGL (F := F) w (borelDiag hy)
    calc x * permGL F w * y
        = x * (permGL F w * Iwasawa.diagGL F n (borelDiag hy)) *
            ((Iwasawa.diagGL F n (borelDiag hy))⁻¹ * y) := by group
      _ = _ := by rw [e]; group
  · rintro ⟨u, hu, t, v, hv, rfl⟩
    exact mem_doubleCoset.2 ⟨u * Iwasawa.diagGL F n t,
      (borel n F).mul_mem (unipotent_le_borel hu) (diagGL_mem_borel t), v, unipotent_le_borel hv,
      rfl⟩

theorem exists_normalForm (g : GL (Fin n) F) :
    ∃ u ∈ Iwasawa.unipotent F n, ∃ t : Fin n → Fˣ, ∃ v ∈ Iwasawa.unipotent F n,
      g = u * Iwasawa.diagGL F n t * permGL F (bruhatCell g) * v :=
  mem_doubleCoset_iff_normalForm.1 (mem_doubleCoset_bruhatCell g)

theorem bruhatCell_normalForm {u v : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n)
    (hv : v ∈ Iwasawa.unipotent F n) (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) :
    bruhatCell (u * Iwasawa.diagGL F n t * permGL F w * v) = w :=
  bruhatCell_eq_iff.2 (mem_doubleCoset_iff_normalForm.2 ⟨u, hu, t, v, hv, rfl⟩)

theorem bruhatCell_diag_perm (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) :
    bruhatCell (Iwasawa.diagGL F n t * permGL F w) = w := by
  have := bruhatCell_normalForm (Iwasawa.unipotent F n).one_mem (Iwasawa.unipotent F n).one_mem t w
  rwa [one_mul, mul_one] at this

end NormalForm

section Minor

def bottomRows (k : Fin n) (a : Fin (k.val + 1)) : Fin n :=
  ⟨n - (k.val + 1) + a.val, by have := a.isLt; have := k.isLt; omega⟩

theorem bottomRows_injective (k : Fin n) : Function.Injective (bottomRows k) := by
  intro a b h
  simp only [bottomRows, Fin.ext_iff] at h
  exact Fin.ext (by omega)

theorem exists_bottomRows_eq {k : Fin n} {a : Fin (k.val + 1)} {s : Fin n}
    (h : bottomRows k a ≤ s) : ∃ b, bottomRows k b = s := by
  rw [Fin.le_def] at h
  simp only [bottomRows] at h
  refine ⟨⟨s.val - (n - (k.val + 1)), by have := s.isLt; have := k.isLt; omega⟩, ?_⟩
  ext
  simp only [bottomRows]
  omega

noncomputable def cellMinor (w : Equiv.Perm (Fin n)) (g : GL (Fin n) F) (k : Fin n) : F :=
  ((g : Matrix (Fin n) (Fin n) F).submatrix (bottomRows k) fun a => w⁻¹ (bottomRows k a)).det

theorem continuous_cellMinor [TopologicalSpace F] [IsTopologicalRing F]
    (w : Equiv.Perm (Fin n)) : Continuous (cellMinor (F := F) w) :=
  continuous_pi fun _ => (Units.continuous_val.matrix_submatrix _ _).matrix_det

theorem submatrix_mul_of_isUpperTriangular {u M : Matrix (Fin n) (Fin n) F}
    (hu : u.IsUpperTriangular) {m p : ℕ} {r : Fin m → Fin n} (hr : Function.Injective r)
    (hup : ∀ a s, r a ≤ s → ∃ b, r b = s) (c : Fin p → Fin n) :
    (u * M).submatrix r c = u.submatrix r r * M.submatrix r c := by
  classical
  ext a b
  simp only [submatrix_apply, mul_apply]
  rw [← Finset.sum_image (s := Finset.univ) (g := r) (fun x _ y _ h => hr h)
    (f := fun s => u (r a) s * M s (c b))]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => ?_
  have hlt : s < r a := by
    by_contra h
    obtain ⟨b', rfl⟩ := hup a s (not_lt.1 h)
    exact hs (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  rw [hu (show id s < id (r a) from hlt), zero_mul]

theorem det_submatrix_of_mem_unipotent {v : GL (Fin n) F} (hv : v ∈ Iwasawa.unipotent F n)
    {m : ℕ} {c : Fin m → Fin n} (hc : Function.Injective c) :
    ((v : Matrix (Fin n) (Fin n) F).submatrix c c).det = 1 := by
  classical
  have hbt : ((v : Matrix (Fin n) (Fin n) F).submatrix c c).BlockTriangular (id ∘ c) :=
    ((Iwasawa.mem_unipotent F n).1 hv).1.submatrix
  rw [hbt.det]
  refine Finset.prod_eq_one fun a ha => ?_
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
  have : Unique {y // (id ∘ c) y = (id ∘ c) x} :=
    ⟨⟨⟨x, rfl⟩⟩, fun y => Subtype.ext (hc y.2)⟩
  rw [det_unique, toSquareBlock_def, of_apply,
    ← Unique.eq_default (⟨x, rfl⟩ : {y // (id ∘ c) y = (id ∘ c) x})]
  simp only [submatrix_apply]
  exact ((Iwasawa.mem_unipotent F n).1 hv).2 (c x)

theorem cellMinor_normalForm (w : Equiv.Perm (Fin n)) {u v : GL (Fin n) F}
    (hu : u ∈ Iwasawa.unipotent F n) (hv : v ∈ Iwasawa.unipotent F n) (t : Fin n → Fˣ) :
    cellMinor w (u * Iwasawa.diagGL F n t * permGL F w * v) =
      fun k => ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) := by
  funext k
  unfold cellMinor
  have hX : ((Iwasawa.diagGL F n t * permGL F w * v : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F).submatrix (bottomRows k) (fun a => w⁻¹ (bottomRows k a)) =
      diagonal (fun a => (t (bottomRows k a) : F)) *
        (v : Matrix (Fin n) (Fin n) F).submatrix (fun a => w⁻¹ (bottomRows k a))
          (fun a => w⁻¹ (bottomRows k a)) := by
    ext a b
    simp only [Units.val_mul, Iwasawa.coe_diagGL, submatrix_apply, diagonal_mul, mul_assoc,
      permGL_mul_apply]
  have hinj : Function.Injective fun a => w⁻¹ (bottomRows k a) :=
    (Equiv.injective _).comp (bottomRows_injective k)
  rw [show u * Iwasawa.diagGL F n t * permGL F w * v =
      u * (Iwasawa.diagGL F n t * permGL F w * v) by group, Units.val_mul,
    submatrix_mul_of_isUpperTriangular ((Iwasawa.mem_unipotent F n).1 hu).1 (bottomRows_injective k)
      (fun a s h => exists_bottomRows_eq h), det_mul, hX, det_mul, det_diagonal,
    det_submatrix_of_mem_unipotent hu (bottomRows_injective k),
    det_submatrix_of_mem_unipotent hv hinj, one_mul, mul_one]

noncomputable def prodFrom (t : Fin n → Fˣ) (s : ℕ) : F :=
  ∏ x ∈ Finset.univ.filter (fun x : Fin n => s ≤ x.val), (t x : F)

theorem prod_bottomRows_eq_prodFrom (t : Fin n → Fˣ) (k : Fin n) :
    ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) = prodFrom t (n - (k.val + 1)) := by
  classical
  unfold prodFrom
  rw [← Finset.prod_image (s := Finset.univ) (g := bottomRows k)
    (fun x _ y _ h => bottomRows_injective k h) (f := fun x => (t x : F))]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨a, rfl⟩
    simp [bottomRows]
  · intro hx
    exact exists_bottomRows_eq (a := ⟨0, Nat.succ_pos _⟩) (by rw [Fin.le_def]; simp only [bottomRows]; omega)

theorem prodFrom_eq_mul (t : Fin n → Fˣ) (x : Fin n) :
    prodFrom t x.val = (t x : F) * prodFrom t (x.val + 1) := by
  classical
  unfold prodFrom
  have e : (Finset.univ.filter fun y : Fin n => x.val ≤ y.val) =
      insert x (Finset.univ.filter fun y : Fin n => x.val + 1 ≤ y.val) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [e, Finset.prod_insert (by simp)]

theorem prodFrom_ne_zero (t : Fin n → Fˣ) (s : ℕ) : prodFrom t s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun x _ => (t x).ne_zero

theorem prodFrom_of_le (t : Fin n → Fˣ) {s : ℕ} (hs : n ≤ s) : prodFrom t s = 1 := by
  unfold prodFrom
  rw [Finset.filter_false_of_mem fun x _ => by have := x.isLt; omega, Finset.prod_empty]

theorem eq_of_prod_bottomRows_eq {t t' : Fin n → Fˣ}
    (h : ∀ k : Fin n, ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) =
      ∏ a : Fin (k.val + 1), (t' (bottomRows k a) : F)) : t = t' := by
  have hall : ∀ s, prodFrom t s = prodFrom (F := F) t' s := by
    intro s
    by_cases hs : s < n
    · have := h ⟨n - 1 - s, by omega⟩
      rw [prod_bottomRows_eq_prodFrom, prod_bottomRows_eq_prodFrom] at this
      have e : n - (n - 1 - s + 1) = s := by omega
      simpa only [e] using this
    · rw [prodFrom_of_le t (by omega), prodFrom_of_le t' (by omega)]
  funext x
  have h1 := prodFrom_eq_mul (F := F) t x
  have h2 := prodFrom_eq_mul (F := F) t' x
  rw [hall, h2, hall (x.val + 1)] at h1
  exact Units.ext (mul_right_cancel₀ (prodFrom_ne_zero t' _) h1.symm)

theorem cellMinor_diag_perm (w : Equiv.Perm (Fin n)) (t : Fin n → Fˣ) :
    cellMinor w (Iwasawa.diagGL F n t * permGL F w) =
      fun k => ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) := by
  have := cellMinor_normalForm w (Iwasawa.unipotent F n).one_mem (Iwasawa.unipotent F n).one_mem t
  rwa [one_mul, mul_one] at this

theorem cellMinor_mul_mul {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)} (hg : bruhatCell g = w)
    {a b : GL (Fin n) F} (ha : a ∈ Iwasawa.unipotent F n) (hb : b ∈ Iwasawa.unipotent F n) :
    cellMinor w (a * g * b) = cellMinor w g := by
  obtain ⟨u, hu, t, v, hv, hg'⟩ := exists_normalForm g
  rw [hg] at hg'
  rw [hg', show a * (u * Iwasawa.diagGL F n t * permGL F w * v) * b =
      (a * u) * Iwasawa.diagGL F n t * permGL F w * (v * b) by group,
    cellMinor_normalForm w ((Iwasawa.unipotent F n).mul_mem ha hu)
      ((Iwasawa.unipotent F n).mul_mem hv hb),
    cellMinor_normalForm w hu hv]

theorem exists_eq_mul_mul_of_cellMinor_eq {g g' : GL (Fin n) F} {w : Equiv.Perm (Fin n)}
    (hg : bruhatCell g = w) (hg' : bruhatCell g' = w) (h : cellMinor w g = cellMinor w g') :
    ∃ a ∈ Iwasawa.unipotent F n, ∃ b ∈ Iwasawa.unipotent F n, g' = a * g * b := by
  obtain ⟨u, hu, t, v, hv, e⟩ := exists_normalForm g
  obtain ⟨u', hu', t', v', hv', e'⟩ := exists_normalForm g'
  rw [hg] at e
  rw [hg'] at e'
  rw [e, e', cellMinor_normalForm w hu hv, cellMinor_normalForm w hu' hv'] at h
  have ht : t = t' := eq_of_prod_bottomRows_eq fun k => congrFun h k
  subst ht
  refine ⟨u' * u⁻¹, (Iwasawa.unipotent F n).mul_mem hu' ((Iwasawa.unipotent F n).inv_mem hu),
    v⁻¹ * v', (Iwasawa.unipotent F n).mul_mem ((Iwasawa.unipotent F n).inv_mem hv) hv', ?_⟩
  rw [e, e']
  group

theorem exists_eq_mul_diag_perm_mul {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)}
    (hg : bruhatCell g = w) :
    ∃ t : Fin n → Fˣ, ∃ a ∈ Iwasawa.unipotent F n, ∃ b ∈ Iwasawa.unipotent F n,
      g = a * (Iwasawa.diagGL F n t * permGL F w) * b := by
  obtain ⟨u, hu, t, v, hv, e⟩ := exists_normalForm g
  rw [hg] at e
  exact ⟨t, u, hu, v, hv, by rw [e]; group⟩

end Minor

end Whittaker

end GroundTheory.Automorphic
