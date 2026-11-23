import Mathlib

open Matrix

namespace GroundTheory.Automorphic

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable (n) (R : Type*) [CommRing R]

def transvectionGL (t : TransvectionStruct n R) : GL n R where
  val := t.toMatrix
  inv := t.inv.toMatrix
  val_inv := TransvectionStruct.mul_inv t
  inv_val := TransvectionStruct.inv_mul t

@[simp]
theorem coe_transvectionGL (t : TransvectionStruct n R) :
    (transvectionGL n R t : Matrix n n R) = t.toMatrix := rfl

def elementarySubgroup : Subgroup (GL n R) :=
  Subgroup.closure (Set.range (transvectionGL n R))

variable {n R}

theorem transvectionGL_mem_elementarySubgroup (t : TransvectionStruct n R) :
    transvectionGL n R t ∈ elementarySubgroup n R :=
  Subgroup.subset_closure ⟨t, rfl⟩

theorem elementarySubgroup_le_ker_det :
    elementarySubgroup n R ≤ (Matrix.GeneralLinearGroup.det : GL n R →* Rˣ).ker := by
  rw [elementarySubgroup, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, TransvectionStruct.det]

theorem coe_list_prod_transvectionGL (L : List (TransvectionStruct n R)) :
    (((L.map (transvectionGL n R)).prod : GL n R) : Matrix n n R) =
      (L.map TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L ih => simp [ih]

theorem list_prod_transvectionGL_mem (L : List (TransvectionStruct n R)) :
    (L.map (transvectionGL n R)).prod ∈ elementarySubgroup n R :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    exact transvectionGL_mem_elementarySubgroup t

theorem mul_transvection_apply (i j : n) (c : R) (M : Matrix n n R) (a b : n) :
    (M * transvection i j c) a b = if b = j then M a j + c * M a i else M a b := by
  split_ifs with h
  · subst h
    exact mul_transvection_apply_same i b a c M
  · exact mul_transvection_apply_of_ne i j a b h c M

theorem transvection_mul_eq_diagonal_update (i j : n) (hij : i ≠ j) (u : Rˣ) :
    transvection i j (u : R) * transvection j i (-(↑u⁻¹ : R)) * transvection i j (u : R) *
      transvection i j (-1) * transvection j i 1 * transvection i j (-1) =
      diagonal (Function.update (Function.update (1 : n → R) i u) j (↑u⁻¹ : R)) := by
  ext a b
  simp only [mul_transvection_apply]
  simp only [diagonal_apply, Function.update_apply, Pi.one_apply, transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hbj : b = j <;> by_cases hbi : b = i <;> by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp [hbj, hbi, hai, haj, hij, Ne.symm hij, @eq_comm _ i, @eq_comm _ j]
  all_goals (try ring_nf)
  all_goals (try simp)

def diagonalGL : (n → Rˣ) →* GL n R where
  toFun d :=
    { val := diagonal fun k => (d k : R)
      inv := diagonal fun k => (↑(d k)⁻¹ : R)
      val_inv := by simp [diagonal_mul_diagonal]
      inv_val := by simp [diagonal_mul_diagonal] }
  map_one' := by ext1; simp
  map_mul' d e := by ext1; simp [diagonal_mul_diagonal]

@[simp]
theorem coe_diagonalGL (d : n → Rˣ) :
    (diagonalGL d : Matrix n n R) = diagonal fun k => (d k : R) := rfl

theorem diagonal_update_mem_elementarySubgroup (i j : n) (hij : i ≠ j) (u : Rˣ) :
    diagonalGL (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) ∈ elementarySubgroup n R := by
  have h : diagonalGL (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) =
      transvectionGL n R ⟨i, j, hij, u⟩ * transvectionGL n R ⟨j, i, hij.symm, -(↑u⁻¹ : R)⟩ *
        transvectionGL n R ⟨i, j, hij, u⟩ * transvectionGL n R ⟨i, j, hij, -1⟩ *
          transvectionGL n R ⟨j, i, hij.symm, 1⟩ * transvectionGL n R ⟨i, j, hij, -1⟩ := by
    ext1
    simp only [Units.val_mul, coe_transvectionGL, TransvectionStruct.toMatrix_mk, coe_diagonalGL]
    rw [transvection_mul_eq_diagonal_update i j hij u]
    congr 1
    funext k
    simp only [Pi.mul_apply, Units.val_mul, Function.update_apply, Pi.one_apply, Pi.mulSingle_apply]
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
  rw [h]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact transvectionGL_mem_elementarySubgroup _

theorem diagonalGL_mem_elementarySubgroup {d : n → Rˣ} (hd : ∏ k, d k = 1) :
    diagonalGL d ∈ elementarySubgroup n R := by
  classical
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · have : d = 1 := funext fun k => isEmptyElim k
    rw [this, map_one]
    exact one_mem _
  have hmem : ∀ i ∈ Finset.univ.erase i₀,
      Pi.mulSingle i (d i) * Pi.mulSingle i₀ (d i)⁻¹ ∈
        (elementarySubgroup n R).comap (diagonalGL (n := n) (R := R)) := fun i hi =>
    diagonal_update_mem_elementarySubgroup i i₀ (Finset.ne_of_mem_erase hi) (d i)
  have hprod := Subgroup.prod_mem _ hmem
  have heq : ∏ i ∈ Finset.univ.erase i₀, (Pi.mulSingle i (d i) * Pi.mulSingle i₀ (d i)⁻¹) = d := by
    funext k
    rw [Finset.prod_apply]
    simp only [Pi.mul_apply, Pi.mulSingle_apply]
    by_cases hk : k = i₀
    · subst hk
      have h1 : ∀ i ∈ Finset.univ.erase k,
          ((if k = i then d i else 1) * if k = k then (d i)⁻¹ else 1) = (d i)⁻¹ := by
        intro i hi
        rw [if_neg (Finset.ne_of_mem_erase hi).symm, if_pos rfl, one_mul]
      rw [Finset.prod_congr rfl h1, Finset.prod_inv_distrib]
      have h2 := Finset.mul_prod_erase Finset.univ d (Finset.mem_univ k)
      rw [hd] at h2
      rw [eq_comm, ← mul_eq_one_iff_eq_inv]
      exact h2
    · have h1 : ∀ i ∈ Finset.univ.erase i₀,
          ((if k = i then d i else 1) * if k = i₀ then (d i)⁻¹ else 1) =
            if k = i then d i else 1 := by
        intro i _
        rw [if_neg hk, mul_one]
      rw [Finset.prod_congr rfl h1, Finset.prod_ite_eq]
      rw [if_pos (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)]
  rw [heq] at hprod
  exact hprod

end CommRing

section Field

variable {F : Type*} [Field F]

theorem mem_elementarySubgroup_of_det_eq_one {g : GL n F}
    (hg : Matrix.GeneralLinearGroup.det g = 1) : g ∈ elementarySubgroup n F := by
  classical
  obtain ⟨L, L', D, hM⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix n n F)
  have hdet : ∏ k, D k = 1 := by
    have h1 : (g : Matrix n n F).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hg, Units.val_one]
    rw [hM, det_mul, det_mul, TransvectionStruct.det_toMatrix_prod,
      TransvectionStruct.det_toMatrix_prod, det_diagonal, one_mul, mul_one] at h1
    exact h1
  have hD : ∀ k, D k ≠ 0 := fun k h0 => by
    have := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hdet] at this
    exact one_ne_zero this
  let d : n → Fˣ := fun k => Units.mk0 (D k) (hD k)
  have hd : ∏ k, d k = 1 := by
    ext
    simp [d, Units.coe_prod, hdet]
  have hg' : g = (L.map (transvectionGL n F)).prod * diagonalGL d *
      (L'.map (transvectionGL n F)).prod := by
    ext1
    simp only [Units.val_mul, coe_list_prod_transvectionGL, coe_diagonalGL]
    rw [hM]
    rfl
  rw [hg']
  exact mul_mem (mul_mem (list_prod_transvectionGL_mem L) (diagonalGL_mem_elementarySubgroup hd))
    (list_prod_transvectionGL_mem L')

end Field

end GroundTheory.Automorphic
