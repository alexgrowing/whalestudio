import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

open MvPolynomial Matrix Equiv

namespace FdegNeZero

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def colExp (j N : ℕ) (l : Fin N) : ℕ := if (l : ℕ) < j then j - 1 - l else N - 1 - l

def blkMat (j : ℕ) (τ : Ψ) : Matrix (Fin N) (Fin N) (Rts Ψ N) :=
  Matrix.of fun i l => if ((i : ℕ) < j ↔ (l : ℕ) < j) then X (τ, i) ^ colExp j N l else 0

def bigMat (j : ℕ) : Matrix (Ψ × Fin N) (Ψ × Fin N) (Rts Ψ N) :=
  Matrix.of fun x l => if x.1 = l.1 ∧ ((x.2 : ℕ) < j ↔ (l.2 : ℕ) < j) then X x ^ colExp j N l.2 else 0

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem det_blkMat (j : ℕ) (hj : j ≤ N) (τ : Ψ) :
    (blkMat (Ψ := Ψ) (N := N) j τ).det = altRho j (yv j hj τ) * altRho (N - j) (zv j τ) := by
  let e : Fin j ⊕ Fin (N - j) ≃ Fin N := finSumFinEquiv.trans (finCongr (by omega))
  rw [← det_submatrix_equiv_self e, ← Matrix.fromBlocks_toBlocks ((blkMat j τ).submatrix e e)]
  have h21 : ((blkMat (Ψ := Ψ) (N := N) j τ).submatrix e e).toBlocks₂₁ = 0 := by
    ext a b
    simp [toBlocks₂₁, blkMat, e]
  rw [h21, det_fromBlocks_zero₂₁]
  congr 1
  · unfold altRho
    congr 1
    refine Matrix.ext fun a b => ?_
    simp [toBlocks₁₁, blkMat, e, yv, colExp]
    rfl
  · unfold altRho
    congr 1
    refine Matrix.ext fun a b => ?_
    simp [toBlocks₂₂, blkMat, e, zv, colExp]
    rw [show N - 1 - (j + (b : ℕ)) = N - j - 1 - b by omega]
    rfl

theorem det_bigMat (j : ℕ) (hj : j ≤ N) : (bigMat (Ψ := Ψ) (N := N) j).det = fibV j hj := by
  have h : bigMat (Ψ := Ψ) (N := N) j =
      (blockDiagonal fun τ => blkMat (Ψ := Ψ) (N := N) j τ).submatrix (Equiv.prodComm Ψ (Fin N))
        (Equiv.prodComm Ψ (Fin N)) := by
    refine Matrix.ext fun x l => ?_
    obtain ⟨x1, x2⟩ := x
    obtain ⟨l1, l2⟩ := l
    simp only [bigMat, blkMat, of_apply, submatrix_apply, Equiv.prodComm_apply, blockDiagonal_apply, Prod.fst_swap,
      Prod.snd_swap]
    by_cases h1 : x1 = l1
    · subst h1
      simp
    · simp [h1]
  rw [h, det_submatrix_equiv_self, det_blockDiagonal, fibV]
  exact Finset.prod_congr rfl fun τ _ => det_blkMat j hj τ

theorem rename_det_bigMat (j : ℕ) (w : Perm (Ψ × Fin N)) (hw : w ∈ G0 j) :
    rename w (bigMat (Ψ := Ψ) (N := N) j).det = ((Perm.sign w : ℤ) : ℚ) • (bigMat j).det := by
  have hw' : ∀ x, (w x).1 = x.1 ∧ (((w x).2 : ℕ) < j ↔ (x.2 : ℕ) < j) := (Finset.mem_filter.mp hw).2
  rw [AlgHom.map_det]
  have h : (rename w : Rts Ψ N →ₐ[ℚ] Rts Ψ N).mapMatrix (bigMat j) = (bigMat j).submatrix w id := by
    refine Matrix.ext fun x l => ?_
    have e : ((w x).1 = l.1 ∧ (((w x).2 : ℕ) < j ↔ (l.2 : ℕ) < j)) ↔
        (x.1 = l.1 ∧ ((x.2 : ℕ) < j ↔ (l.2 : ℕ) < j)) := by rw [(hw' x).1, (hw' x).2]
    simp only [AlgHom.mapMatrix_apply, map_apply, bigMat, of_apply, submatrix_apply, id, e]
    split_ifs <;> simp
  rw [h, det_permute, MvPolynomial.smul_eq_C_mul]
  congr 1

theorem antisym_fibV (j : ℕ) (hj : j ≤ N) :
    antisym (G0 j) (fibV (Ψ := Ψ) j hj) = ((G0 (Ψ := Ψ) (N := N) j).card : ℚ) • fibV j hj := by
  rw [antisym, ← det_bigMat j hj, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [rename_det_bigMat j w hw, smul_smul, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

def rev (j : ℕ) (hj : j ≤ N) (i : Fin N) : Fin N :=
  ⟨if (i : ℕ) < j then j - 1 - i else N - 1 + j - i, by split_ifs <;> omega⟩

theorem rev_rev (j : ℕ) (hj : j ≤ N) (i : Fin N) : rev j hj (rev j hj i) = i := by
  apply Fin.ext
  simp only [rev]
  split_ifs <;> omega

def rho (j : ℕ) (hj : j ≤ N) : Perm (Ψ × Fin N) :=
  Function.Involutive.toPerm (fun x => (x.1, rev j hj x.2)) fun x => by simp [rev_rev]

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem rho_apply (j : ℕ) (hj : j ≤ N) (x : Ψ × Fin N) : rho j hj x = (x.1, rev j hj x.2) := rfl

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem rho_mem (j : ℕ) (hj : j ≤ N) (l : Ψ × Fin N) :
    (rho j hj l).1 = l.1 ∧ ((((rho j hj l).2 : Fin N) : ℕ) < j ↔ (l.2 : ℕ) < j) := by
  simp only [rho_apply, rev, true_and]
  split_ifs <;> omega

theorem prod_bigMat_of (j : ℕ) (σ : Perm (Ψ × Fin N))
    (hσ : ∀ l, (σ l).1 = l.1 ∧ (((σ l).2 : ℕ) < j ↔ (l.2 : ℕ) < j)) :
    ∏ l, bigMat (Ψ := Ψ) (N := N) j (σ l) l = monomial (∑ l, Finsupp.single (σ l) (colExp j N l.2)) 1 := by
  rw [monomial_sum_one]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [bigMat, (hσ l).1, (hσ l).2, X_pow_eq_monomial]

theorem sum_single_apply (j : ℕ) (σ : Perm (Ψ × Fin N)) (l : Ψ × Fin N) :
    (∑ l', Finsupp.single (σ l') (colExp j N l'.2)) (σ l) = colExp j N l.2 := by
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, σ.injective.eq_iff]

theorem sum_single_rho (j : ℕ) (hj : j ≤ N) :
    (∑ l, Finsupp.single (rho (Ψ := Ψ) j hj l) (colExp j N l.2)) = delta0 j := by
  refine Finsupp.ext fun x => ?_
  obtain ⟨l, rfl⟩ := (rho (Ψ := Ψ) j hj).surjective x
  rw [sum_single_apply]
  simp only [delta0, Finsupp.coe_equivFunOnFinite_symm, rho_apply, rev, colExp]
  split_ifs <;> omega

theorem coeff_det_bigMat (j : ℕ) (hj : j ≤ N) :
    coeff (delta0 j) (bigMat (Ψ := Ψ) (N := N) j).det = ((Perm.sign (rho (Ψ := Ψ) j hj) : ℤ) : ℚ) := by
  rw [det_apply, coeff_sum, Finset.sum_eq_single (rho j hj)]
  · rw [Units.smul_def, coeff_smul, prod_bigMat_of j _ (rho_mem j hj), coeff_monomial,
      if_pos (sum_single_rho j hj)]
    simp
  · intro σ _ hne
    rw [Units.smul_def, coeff_smul]
    by_cases hσ : ∀ l, (σ l).1 = l.1 ∧ (((σ l).2 : ℕ) < j ↔ (l.2 : ℕ) < j)
    · rw [prod_bigMat_of j σ hσ, coeff_monomial, if_neg, smul_zero]
      intro hm
      apply hne
      refine Equiv.ext fun l => Prod.ext ?_ (Fin.ext ?_)
      · rw [(hσ l).1, rho_apply]
      · have h1 := congrArg (fun m : Ψ × Fin N →₀ ℕ => m (σ l)) hm
        have h2 := (hσ l).2
        rw [sum_single_apply] at h1
        simp only [delta0, Finsupp.coe_equivFunOnFinite_symm, colExp] at h1
        simp only [rho_apply, rev]
        have h3 := (σ l).2.2
        have h4 := l.2.2
        split_ifs at h1 ⊢ <;> omega
    · obtain ⟨l, hl⟩ := not_forall.mp hσ
      rw [Finset.prod_eq_zero (Finset.mem_univ l) (by simp only [bigMat, of_apply, if_neg hl]), coeff_zero,
        smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem proof : FdegNeZero.Statement := by
  intro Ψ _ _ N j hj
  rw [fdeg, antisym_fibV j hj, coeff_smul, ← det_bigMat j hj, coeff_det_bigMat j hj, smul_eq_mul]
  refine mul_ne_zero ?_ ?_
  · exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, by simp [G0]⟩)
  · exact Int.cast_ne_zero.mpr (Units.ne_zero _)

end FdegNeZero

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
