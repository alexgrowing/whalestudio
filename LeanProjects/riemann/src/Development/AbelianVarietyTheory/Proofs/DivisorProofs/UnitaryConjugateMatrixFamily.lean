import Mathlib

open Matrix

namespace GlobalTheory

theorem rectId_eq_fromCols (R : Type) [Semiring R] (N r : ℕ) :
    (Matrix.of fun (j : Fin N) (k : Fin (N + r)) => if (j : ℕ) = (k : ℕ) then (1 : R) else 0)
      = (Matrix.fromCols (1 : Matrix (Fin N) (Fin N) R) (0 : Matrix (Fin N) (Fin r) R)).submatrix
          id finSumFinEquiv.symm := by
  ext j k
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with k | k
  · simp [Matrix.one_apply, Fin.ext_iff]
  · have := j.2
    have h : (j : ℕ) ≠ N + k := by omega
    simp [h]

theorem exists_frames_extend (K : Type) [Field K] (N n : ℕ) (g : Matrix (Fin N) (Fin n) K)
    (M : Matrix (Fin n) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hN : N ≤ n)
    (hM : M.det ≠ 0)
    (hg : g * M = (Matrix.of fun (j : Fin N) (k : Fin n) =>
      if (j : ℕ) = (k : ℕ) then (1 : K) else 0))
    (hA : ∀ σ, (A σ).det ≠ 0)
    (hU : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ,
      A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U) :
    ∃ A' : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, (A' σ).det ≠ 0) ∧
      (∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
        A' ((starRingEnd ℂ).comp σ) = (A' σ).map (starRingEnd ℂ) * U) ∧
      ∀ σ : K →+* ℂ, g.map σ * A' σ = A σ * (Matrix.of fun (j : Fin N) (k : Fin n) =>
        if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hN
  let E : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin (N + r)) (Fin (N + r)) ℂ := fun B =>
    (Matrix.fromBlocks B 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm
  have Edet : ∀ B, (E B).det = B.det := fun B => by
    simp [E, Matrix.det_submatrix_equiv_self]
  have Emul : ∀ B C, E (B * C) = E B * E C := fun B C => by
    simp [E, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  have Eone : E 1 = 1 := by simp [E]
  have Estar : ∀ B, E (star B) = star (E B) := fun B => by
    simp [E, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.fromBlocks_conjTranspose]
  have Emap : ∀ B, E (B.map (starRingEnd ℂ)) = (E B).map (starRingEnd ℂ) := fun B => by
    simp only [E]
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
    simp
  refine ⟨fun σ => M.map σ * E (A σ), fun σ => ?_, fun σ => ?_, fun σ => ?_⟩
  · rw [Matrix.det_mul, Edet]
    refine mul_ne_zero ?_ (hA σ)
    have h := σ.map_det M
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (_root_.map_ne_zero σ).2 hM
  · obtain ⟨U, hUm, hUe⟩ := hU σ
    refine ⟨E U, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hUm ⊢
      rw [← Estar, ← Emul, hUm, Eone]
    · simp only
      rw [hUe, Emul, Emap, Matrix.map_mul, Matrix.map_map, Matrix.mul_assoc]
      rfl
  · simp only
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, hg]
    have h1 : (Matrix.of fun (j : Fin N) (k : Fin (N + r)) =>
        if (j : ℕ) = (k : ℕ) then (1 : K) else 0).map σ
        = (Matrix.of fun (j : Fin N) (k : Fin (N + r)) =>
        if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) := by
      ext j k
      simp [apply_ite σ]
    rw [h1, rectId_eq_fromCols]
    simp only [E]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
    ext j k
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
    rcases k with k | k
    · simp [Matrix.mul_apply, Matrix.one_apply]
    · simp [Matrix.mul_apply]

end GlobalTheory
