import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.IsIrreducibleIff

open UpperTheory.V.AlgebraTools

private lemma indSymp_two {R : Type} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    A.transpose * !![0, 1; -1, 0] * A = A.det • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem UpperTheory.V.AlgebraTools.indSymp :
    ∀ {R G : Type} [CommRing R] [Group G] (H : Subgroup G) (s : G), H.index = 2 → s ∉ H → ∀ (r : H →* GL (Fin 2) R) (θ : G →* Rˣ) (I : G →* GL (Fin 2 ⊕ Fin 2) R), (∀ h : H, (r h : Matrix (Fin 2) (Fin 2) R).det = θ h) → (∀ h h' : H, (h' : G) = s⁻¹ * h * s → (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = Matrix.fromBlocks (r h : Matrix (Fin 2) (Fin 2) R) 0 0 (r h' : Matrix (Fin 2) (Fin 2) R)) → (∀ t : H, (t : G) = s * s → (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = Matrix.fromBlocks 0 (r t : Matrix (Fin 2) (Fin 2) R) 1 0) → ∀ g, (I g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * Matrix.fromBlocks !![0, 1; -1, 0] 0 0 ((θ s : R) • !![0, 1; -1, 0]) * (I g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = (θ g : R) • Matrix.fromBlocks !![0, 1; -1, 0] 0 0 ((θ s : R) • !![0, 1; -1, 0]) := by
  intro R G _ _ H s hi hs r θ I hdet hH hS
  have hN : H.Normal := Subgroup.normal_of_index_eq_two hi
  set J : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0] with hJ
  have h2 : ∀ A : Matrix (Fin 2) (Fin 2) R, A.transpose * J * A = A.det • J :=
    fun A => indSymp_two A
  set B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
    Matrix.fromBlocks J 0 0 ((θ s : R) • J) with hB
  have key1 : ∀ h ∈ H, (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * B *
      (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = (θ h : R) • B := by
    intro h hh
    have hh' : s⁻¹ * h * s ∈ H := by simpa using hN.conj_mem h hh s⁻¹
    have e := hH ⟨h, hh⟩ ⟨_, hh'⟩ rfl
    have d1 := hdet ⟨h, hh⟩
    have d2 := hdet ⟨_, hh'⟩
    have d3 : θ (s⁻¹ * h * s) = θ h := by
      simp only [map_mul, map_inv]
      rw [mul_right_comm, inv_mul_cancel, one_mul]
    simp only [d3] at d1 d2 e
    rw [e, hB, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      smul_zero, Matrix.mul_smul, Matrix.smul_mul, h2, d1, d2]
    rw [smul_comm (θ s : R)]
  have key2 : (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * B *
      (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = (θ s : R) • B := by
    have ht : s * s ∈ H := Subgroup.mul_self_mem_of_index_two hi s
    have e := hS ⟨_, ht⟩ rfl
    have d := hdet ⟨_, ht⟩
    simp only [map_mul, Units.val_mul] at d
    rw [e, hB, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
      smul_zero, Matrix.mul_smul, Matrix.smul_mul, h2, d, smul_smul]
  intro g
  by_cases hg : g ∈ H
  · exact key1 g hg
  · have hh : g * s⁻¹ ∈ H := by
      rw [Subgroup.mul_mem_iff_of_index_two hi]
      simp [hg, hs]
    have eg : g = (g * s⁻¹) * s := by group
    have k := key1 _ hh
    generalize g * s⁻¹ = h at eg k
    subst eg
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.transpose_mul]
    calc _ = (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose *
          ((I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * B *
          (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) *
          (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by
            rw [k, Matrix.mul_smul, Matrix.smul_mul, key2, smul_smul]
