import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pBlockMat :
    BlockMat := by
  intro R _ σ hσ c x y hc h m
  let b : Matrix (Fin 2) (Fin 2) R := !![x, -σ y; y, σ x]
  let b' : Matrix (Fin 2) (Fin 2) R := !![c * σ x, c * σ y; -(c * y), c * x]
  let M : Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R :=
    fromBlocks 1 0 0 (blockDiagonal fun _ => b)
  let M' : Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R :=
    fromBlocks 1 0 0 (blockDiagonal fun _ => b')
  let e : Fin 1 ⊕ (Fin 2 × Fin m) ≃ Fin (2 * m + 1) :=
    ((Equiv.refl (Fin 1)).sumCongr finProdFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  have hbd : (fromBlocks 1 0 0 (blockDiagonal fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) R)) :
      Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R) = 1 := by
    have h1 : (blockDiagonal fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) R)) = 1 :=
      blockDiagonal_one
    rw [h1, fromBlocks_one]
  have hbb' : b * b' = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, b', Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | ring
  have hb'b : b' * b = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, b', Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | ring
  have hu : (b.map σ)ᵀ * diagonal (fun _ : Fin 2 => c) * b = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, Matrix.mul_apply, Fin.sum_univ_two, hσ] <;>
      first | linear_combination h | ring
  have hM : M * M' = 1 := by
    simp only [M, M', fromBlocks_multiply]
    rw [← blockDiagonal_mul]
    simp only [hbb', Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    exact hbd
  have hM' : M' * M = 1 := by
    simp only [M, M', fromBlocks_multiply]
    rw [← blockDiagonal_mul]
    simp only [hb'b, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    exact hbd
  have hD : (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e =
      Sum.elim (fun _ => 1) (fun _ => c) := by
    funext p
    rcases p with p | p
    · have hp : p = 0 := Subsingleton.elim _ _
      subst hp
      simp [e]
      intro hne
      exact (hne (Fin.ext (by simp))).elim
    · simp [e]
  have hd2 : (diagonal fun _ : Fin 2 × Fin m => c) =
      blockDiagonal fun _ : Fin m => diagonal fun _ : Fin 2 => c := by
    rw [blockDiagonal_diagonal]
  have hcore : (M.map σ)ᵀ *
      diagonal ((fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e) * M = 1 := by
    rw [hD, ← fromBlocks_diagonal]
    simp only [M, fromBlocks_map, fromBlocks_transpose, blockDiagonal_map _ _ (map_zero σ),
      blockDiagonal_transpose, hd2]
    simp only [fromBlocks_multiply, Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
    rw [← blockDiagonal_mul, ← blockDiagonal_mul]
    simp only [hu]
    simpa using hbd
  have hbS : ∀ (S : Subring R), x ∈ S → y ∈ S → σ x ∈ S → σ y ∈ S → c ∈ S →
      (∀ i j, b i j ∈ S) ∧ ∀ i j, b' i j ∈ S := by
    intro S hx hy hsx hsy hcS
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [b] <;>
        first | assumption | exact S.neg_mem hsy
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [b'] <;>
        first | exact S.neg_mem (S.mul_mem hcS hy) | exact S.mul_mem hcS hsx | exact S.mul_mem hcS hsy | exact S.mul_mem hcS hx | exact S.mul_mem hcS hy
  have hblk : ∀ (S : Subring R) (N : Matrix (Fin 2) (Fin 2) R), (∀ i j, N i j ∈ S) →
      ∀ p q, (fromBlocks 1 0 0 (blockDiagonal fun _ : Fin m => N) :
        Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R) p q ∈ S := by
    intro S N hN p q
    rcases p with p | ⟨i, k⟩ <;> rcases q with q | ⟨j, l⟩
    · simp only [fromBlocks_apply₁₁, one_apply]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    · simp only [fromBlocks_apply₁₂, Matrix.zero_apply]
      exact S.zero_mem
    · simp only [fromBlocks_apply₂₁, Matrix.zero_apply]
      exact S.zero_mem
    · simp only [fromBlocks_apply₂₂, blockDiagonal_apply]
      split_ifs
      · exact hN _ _
      · exact S.zero_mem
  refine ⟨⟨reindex e e M, reindex e e M', ?_, ?_⟩, ?_, ?_⟩
  · rw [reindex_apply, reindex_apply, submatrix_mul_equiv, hM, submatrix_one_equiv]
  · rw [reindex_apply, reindex_apply, submatrix_mul_equiv, hM', submatrix_one_equiv]
  · have hDD : diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) =
        (diagonal ((fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e)).submatrix
          e.symm e.symm := by
      rw [submatrix_diagonal_equiv]
      congr 1
      funext i
      simp
    show ((reindex e e M).map σ)ᵀ *
        diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) * reindex e e M = 1
    rw [hDD, reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv,
      submatrix_mul_equiv, hcore, submatrix_one_equiv]
  · intro S hx hy hsx hsy hcS i j
    obtain ⟨h1, h2⟩ := hbS S hx hy hsx hsy hcS
    exact ⟨hblk S b h1 _ _, hblk S b' h2 _ _⟩
