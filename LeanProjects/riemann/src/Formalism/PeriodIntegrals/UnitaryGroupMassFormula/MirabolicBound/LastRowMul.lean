import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Development

namespace PI.GGMirBoundW

open Matrix Formalism.L2.SG.GGMirabolic

noncomputable section

open Classical

section Entries

variable {F : Type} [Field F] [Fintype F] {n : ℕ}

@[simp] theorem blkM_cc (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    blkM A (Fin.castSucc i) (Fin.castSucc j) = A i j := by
  simp [blkM, finSumFinEquiv_symm_apply_castSucc]

@[simp] theorem blkM_cl (A : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    blkM A (Fin.castSucc i) (Fin.last n) = 0 := by
  simp [blkM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem blkM_lc (A : Matrix (Fin n) (Fin n) F) (j : Fin n) :
    blkM A (Fin.last n) (Fin.castSucc j) = 0 := by
  simp [blkM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem blkM_ll (A : Matrix (Fin n) (Fin n) F) :
    blkM A (Fin.last n) (Fin.last n) = 1 := by
  simp [blkM, finSumFinEquiv_symm_last]

@[simp] theorem colM_cc (x : Fin n → F) (i j : Fin n) :
    colM x (Fin.castSucc i) (Fin.castSucc j) = (1 : Matrix (Fin n) (Fin n) F) i j := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc]

@[simp] theorem colM_cl (x : Fin n → F) (i : Fin n) :
    colM x (Fin.castSucc i) (Fin.last n) = x i := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem colM_lc (x : Fin n → F) (j : Fin n) :
    colM x (Fin.last n) (Fin.castSucc j) = 0 := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem colM_ll (x : Fin n → F) :
    colM x (Fin.last n) (Fin.last n) = 1 := by
  simp [colM, finSumFinEquiv_symm_last]

theorem E_val (A : GL (Fin n) F) : ((E F n A : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
    blkM (A : Matrix (Fin n) (Fin n) F) := rfl

theorem col_val (x : Fin n → F) : ((col x : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
    colM x := rfl

end Entries

theorem blkFacts : UnitriangularBlockExtension := by
  intro F _ _ n u hu
  obtain ⟨hd, hl⟩ := hu
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [E_val]
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simpa using hd i
  · rw [E_val]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast j => simp
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)
      | cast j =>
        simp only [blkM_cc]
        exact hl i j (Fin.castSucc_lt_castSucc_iff.mp hij)
  · rw [E_val]
    unfold superdiag
    simp [Fin.sum_univ_castSucc]

theorem colFacts : ColFacts := by
  intro F _ _ n x
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [col_val]
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  · rw [col_val]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast j => simp
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)
      | cast j =>
        simp only [colM_cc]
        exact Matrix.one_apply_ne (ne_of_gt (Fin.castSucc_lt_castSucc_iff.mp hij))
  · rw [col_val]
    unfold superdiag
    have h0 : ∀ i j : Fin (n + 1),
        (if (j : ℕ) = (i : ℕ) + 1 then (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j else 0) = 0 := by
      intro i j
      split_ifs with h
      · rw [Matrix.one_apply_ne]
        intro e; subst e; omega
      · rfl
    have hl : ∀ i : Fin (n + 1), (n = (i : ℕ)) ↔ (i = Fin.last n) := by
      intro i; rw [Fin.ext_iff, Fin.val_last]; omega
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.sum_univ_castSucc (n := n + 1), colM_cc, colM_cl, colM_lc, colM_ll, Fin.val_castSucc,
      Fin.val_last, h0, ite_self, add_left_inj, hl]
    simp

theorem conjCol : ConjCol := by
  intro F _ _ n A x
  ext : 1
  simp only [Units.val_mul, E_val, col_val, blkM, colM]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp
  · simp

theorem baseProp : BaseProp := by
  intro F _ _ ψ₀ _ V _ _ π ℓ hℓ _
  have hD : D F (0 + 1) = 1 := by simp [D]
  show ∃ p : Fin (D F (0 + 1)) → GL (Fin (0 + 1)) F, _
  rw [hD]
  refine ⟨fun _ => 1, fun _ j => ?_, ?_⟩
  · simp only [Units.val_one]
    rw [Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · rw [linearIndependent_unique_iff]
    show ℓ ∘ₗ π 1 ≠ 0
    rw [map_one]
    intro h
    apply hℓ
    ext v
    simpa using LinearMap.congr_fun h v

theorem lastRowE_E {F : Type} [Field F] [Fintype F] {n : ℕ} (A : GL (Fin n) F) : LastRowE (E F n A) := by
  intro j
  rw [E_val]
  induction j using Fin.lastCases with
  | last => simp
  | cast j => simp [Fin.castSucc_ne_last]

theorem lastRow_mul {F : Type} [Field F] [Fintype F] {n : ℕ} {p : GL (Fin (n + 1)) F} (hp : LastRowE p)
    (g : GL (Fin (n + 1)) F) (j : Fin (n + 1)) :
    ((p * g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j := by
  have h2 : ∀ l, (p : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) l = if l = Fin.last n then 1 else 0 := hp
  rw [Units.val_mul, Matrix.mul_apply]
  simp only [h2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

end PI.GGMirBoundW
