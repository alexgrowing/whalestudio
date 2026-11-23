import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

variable {k : ℕ}

theorem eBs_X {n ρ' : ℕ} (p : Fin (2 * (n + ρ') + k + 1)) (hp : p.val < n) :
    (U.eB k n ρ').symm p = Sum.inl (Sum.inl ⟨p.val, hp⟩) := by
  rw [Equiv.symm_apply_eq]
  ext
  simp [U.eB]

theorem eBs_V {n ρ' : ℕ} (p : Fin (2 * (n + ρ') + k + 1)) (hp : n ≤ p.val) (hp' : p.val < n + (2 * ρ' + k + 1)) :
    (U.eB k n ρ').symm p = Sum.inl (Sum.inr ⟨p.val - n, by omega⟩) := by
  rw [Equiv.symm_apply_eq]
  ext
  simp [U.eB]
  omega

theorem eBs_S {n ρ' : ℕ} (p : Fin (2 * (n + ρ') + k + 1)) (hp : n + (2 * ρ' + k + 1) ≤ p.val) :
    (U.eB k n ρ').symm p = Sum.inr ⟨p.val - (n + (2 * ρ' + k + 1)), by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  ext
  simp [U.eB]
  omega

theorem eX {n ρ' : ℕ} (p : Fin (2 * (n + ρ') + k + 1)) (hp : p.val < n) :
    U.eB k n ρ' (Sum.inl (Sum.inl ⟨p.val, hp⟩)) = p := by
  ext
  simp [U.eB]

theorem eV {n ρ' : ℕ} (p : Fin (2 * (n + ρ') + k + 1)) (hp : n ≤ p.val) (hp' : p.val < n + (2 * ρ' + k + 1)) :
    U.eB k n ρ' (Sum.inl (Sum.inr ⟨p.val - n, by omega⟩)) = p := by
  ext
  simp [U.eB]
  omega

theorem eS {n ρ' : ℕ} (p : Fin (2 * (n + ρ') + k + 1)) (hp : n + (2 * ρ' + k + 1) ≤ p.val) :
    U.eB k n ρ' (Sum.inr ⟨p.val - (n + (2 * ρ' + k + 1)), by have := p.isLt; omega⟩) = p := by
  ext
  simp [U.eB]
  omega

local macro "blks" : tactic => `(tactic| simp only [Ux3.block3_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
  Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
  Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr])

private theorem blk3_unipotent_apply_superdiag_eq_zero {n ρ' : ℕ} (A12 : Matrix (Fin n) (Fin (2 * ρ' + k + 1)) ℂ) (A13 : Matrix (Fin n) (Fin n) ℂ)
    (A23 : Matrix (Fin (2 * ρ' + k + 1)) (Fin n) ℂ) (p q : Fin (2 * (n + ρ') + k + 1))
    (hq : q.val = p.val + 1) (hqr : q.val < n + ρ') (hpn : p.val + 1 ≠ n) :
    U.blk3 1 A12 A13 0 1 A23 0 0 1 p q = 0 := by
  by_cases hqn : q.val < n
  · have hp : p.val < n := by omega
    rw [← eX q hqn, ← eX p hp, Ux3.block3_apply]
    blks
    exact Matrix.one_apply_ne (by simp only [ne_eq, Fin.mk.injEq]; omega)
  · have hp1 : n ≤ p.val := by omega
    have hp2 : p.val < n + (2 * ρ' + k + 1) := by omega
    have hq1 : n ≤ q.val := by omega
    have hq2 : q.val < n + (2 * ρ' + k + 1) := by omega
    rw [← eV q hq1 hq2, ← eV p hp1 hp2, Ux3.block3_apply]
    blks
    exact Matrix.one_apply_ne (by simp only [ne_eq, Fin.mk.injEq]; omega)

private theorem blk3_mulVec_eB_inr_eq_zero_of_inWb {n ρ' : ℕ} (A12 : Matrix (Fin n) (Fin (2 * ρ' + k + 1)) ℂ) (A13 : Matrix (Fin n) (Fin n) ℂ)
    (A23 : Matrix (Fin (2 * ρ' + k + 1)) (Fin n) ℂ) (z : Fin (2 * (n + ρ') + k + 1) → ℂ) (hz : inWb k (n + ρ') z)
    (v : Fin (2 * ρ' + k + 1)) (hv : v.val < ρ') :
    (U.blk3 1 A12 A13 0 1 A23 0 0 1 *ᵥ z) (U.eB k n ρ' (Sum.inl (Sum.inr v))) = 0 := by
  unfold Formalism.QuantumDeterminants.inWb at hz
  have hS : ∀ b : Fin n, z (U.eB k n ρ' (Sum.inr b)) = 0 := fun b =>
    hz _ (Or.inr (by simp [U.eB] <;> omega))
  simp only [Matrix.mulVec, dotProduct]
  rw [← (U.eB k n ρ').sum_comp]
  simp only [Ux3.block3_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add, hS, mul_zero, add_zero, Matrix.one_apply, ite_mul, one_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact hz _ (Or.inl (by simp [U.eB] <;> omega))

private theorem blk3_mulVec_eB_inl_eq_mulVec_lowV {n ρ' : ℕ} (A12 : Matrix (Fin n) (Fin (2 * ρ' + k + 1)) ℂ) (A13 : Matrix (Fin n) (Fin n) ℂ)
    (A23 : Matrix (Fin (2 * ρ' + k + 1)) (Fin n) ℂ) (z : Fin (2 * (n + ρ') + k + 1) → ℂ) (hz : inWb k (n + ρ') z)
    (i : Fin n) :
    (U.blk3 1 A12 A13 0 1 A23 0 0 1 *ᵥ z) (U.eB k n ρ' (Sum.inl (Sum.inl i))) = (A12 *ᵥ U.lowV k n ρ' z) i := by
  unfold Formalism.QuantumDeterminants.inWb at hz
  have hX : ∀ b : Fin n, z (U.eB k n ρ' (Sum.inl (Sum.inl b))) = 0 := fun b =>
    hz _ (Or.inl (by simp [U.eB] <;> omega))
  have hS : ∀ b : Fin n, z (U.eB k n ρ' (Sum.inr b)) = 0 := fun b =>
    hz _ (Or.inr (by simp [U.eB] <;> omega))
  have hV : ∀ v : Fin (2 * ρ' + k + 1), z (U.eB k n ρ' (Sum.inl (Sum.inr v))) = U.lowV k n ρ' z v := fun v => by
    simp only [U.lowV]
    congr 1
  simp only [Matrix.mulVec, dotProduct]
  rw [← (U.eB k n ρ').sum_comp]
  simp only [Ux3.block3_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, hX, hS, hV, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero]

theorem ell_uni {n ρ' : ℕ} (z : Fin (2 * (n + ρ') + k + 1) → ℂ) (hz : inWb k (n + ρ') z)
    (A12 : Matrix (Fin n) (Fin (2 * ρ' + k + 1)) ℂ) (A13 : Matrix (Fin n) (Fin n) ℂ)
    (A23 : Matrix (Fin (2 * ρ' + k + 1)) (Fin n) ℂ) :
    ell k (n + ρ') z (U.blk3 1 A12 A13 0 1 A23 0 0 1) =
      if h : 0 < n then
        (if hρ : 0 < ρ' then A12 ⟨n - 1, by omega⟩ ⟨0, by omega⟩ else (A12 *ᵥ U.lowV k n ρ' z) ⟨n - 1, by omega⟩)
      else 0 := by
  unfold Formalism.QuantumDeterminants.ell
  by_cases hn : 0 < n
  · rw [dif_pos hn]
    rw [Finset.sum_eq_single (⟨n - 1, by omega⟩ : Fin (n + ρ'))]
    · by_cases hρ : 0 < ρ'
      · have hlt : (⟨n - 1, by omega⟩ : Fin (n + ρ')).val + 1 < n + ρ' := by
          show n - 1 + 1 < n + ρ'
          omega
        rw [dif_pos hρ, dif_pos hlt]
        rw [← eX (Formalism.QuantumDeterminants.eI k (n + ρ') ⟨n - 1, by omega⟩) (by show n - 1 < n; omega),
          ← eV (Formalism.QuantumDeterminants.eI k (n + ρ') ⟨(⟨n - 1, by omega⟩ : Fin (n + ρ')).val + 1, hlt⟩)
            (by show n ≤ n - 1 + 1; omega) (by show n - 1 + 1 < n + (2 * ρ' + k + 1); omega),
          Ux3.block3_apply]
        blks
        congr <;> simp [Formalism.QuantumDeterminants.eI] <;> omega
      · have hlt : ¬ ((⟨n - 1, by omega⟩ : Fin (n + ρ')).val + 1 < n + ρ') := by
          show ¬ (n - 1 + 1 < n + ρ')
          omega
        rw [dif_neg hρ, dif_neg hlt]
        rw [← eX (Formalism.QuantumDeterminants.eI k (n + ρ') ⟨n - 1, by omega⟩) (by show n - 1 < n; omega)]
        rw [blk3_mulVec_eB_inl_eq_mulVec_lowV A12 A13 A23 z hz]
        rfl
    · intro b _ hb
      have hb' : b.val ≠ n - 1 := fun h => hb (Fin.ext h)
      by_cases h : b.val + 1 < n + ρ'
      · rw [dif_pos h]
        exact blk3_unipotent_apply_superdiag_eq_zero A12 A13 A23 _ _ (by show b.val + 1 = b.val + 1; rfl) h (by show b.val + 1 ≠ n; omega)
      · rw [dif_neg h]
        rw [← eV (Formalism.QuantumDeterminants.eI k (n + ρ') b) (by show n ≤ b.val; omega)
          (by show b.val < n + (2 * ρ' + k + 1); omega)]
        exact blk3_mulVec_eB_inr_eq_zero_of_inWb A12 A13 A23 z hz _ (by show b.val - n < ρ'; omega)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hn]
    apply Finset.sum_eq_zero
    intro b _
    by_cases h : b.val + 1 < n + ρ'
    · rw [dif_pos h]
      exact blk3_unipotent_apply_superdiag_eq_zero A12 A13 A23 _ _ (by show b.val + 1 = b.val + 1; rfl) h (by show b.val + 1 ≠ n; omega)
    · rw [dif_neg h]
      rw [← eV (Formalism.QuantumDeterminants.eI k (n + ρ') b) (by show n ≤ b.val; omega)
        (by show b.val < n + (2 * ρ' + k + 1); omega)]
      exact blk3_mulVec_eB_inr_eq_zero_of_inWb A12 A13 A23 z hz _ (by show b.val - n < ρ'; omega)

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

variable {k j ρ : ℕ}

section chars

open Dx2.Split

private theorem hpk_apply_zero_col (ρ : ℕ) (c : Fin (2 * (1 + ρ) + k + 1)) :
    Formalism.QuantumDeterminants.Hpk k (1 + ρ) c ⟨0, by omega⟩ = if c = ⟨2 * (1 + ρ) + k, by omega⟩ then 1 else 0 := by
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | (exfalso; omega)

theorem ell_Rj (x : U.RC k j (1 + ρ)) (z : Fin (2 * (j + (1 + ρ)) + k + 1) → ℂ) (hz : inWb k (j + (1 + ρ)) z) :
    ell k (j + (1 + ρ)) z (U.Rn k j (1 + ρ) x) = if h : 0 < j then -star (cb x ⟨0, h⟩) else 0 := by
  unfold U.Rn
  rw [ell_uni z hz]
  by_cases hj : 0 < j
  · rw [dif_pos hj, dif_pos hj, dif_pos (show 0 < 1 + ρ by omega)]
    rw [Matrix.neg_apply, neg_inj]
    simp only [Matrix.mul_apply, G.wMat, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.conjTranspose_apply, hpk_apply_zero_col, mul_ite, mul_one, mul_zero]
    simp only [cb]
    rw [show (⟨2 * (1 + ρ) + k, by omega⟩ : Fin (2 * (1 + ρ) + k + 1)) = U.eB k 1 ρ (Sum.inr 0) from
        Fin.ext (by simp [U.eB] <;> omega),
      show (⟨j - 1, by omega⟩ : Fin j).rev = ⟨0, hj⟩ from Fin.ext (by simp [Fin.val_rev] <;> omega)]
  · rw [dif_neg hj, dif_neg hj]

private theorem wMat_mul_conjTranspose_mul_apply_last {N m : ℕ} (w : Fin N → Fin (m + 1) → ℂ) (H : Matrix (Fin N) (Fin N) ℂ)
    (i : Fin (m + 1)) (hi : i.val = m) (c : Fin N) :
    (G.wMat (m + 1) * (Matrix.of w)ᴴ * H) i c = Matrix.vecMul (star (fun d => w d 0)) H c := by
  have hr : i.rev = 0 := Fin.ext (by simp [Fin.val_rev] <;> omega)
  simp only [Matrix.mul_apply, G.wMat, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Matrix.conjTranspose_apply, hr, Matrix.vecMul, dotProduct, Pi.star_apply]

theorem ell_RX (x : U.RC k j (1 + ρ)) (y : U.RC k 1 ρ) (z : Fin (2 * (j + 1 + ρ) + k + 1) → ℂ)
    (hz : inWb k (j + 1 + ρ) z) :
    ell k (j + 1 + ρ) z (U.Rn k (j + 1) ρ (XC x y)) =
      if hρ : 0 < ρ then -Matrix.vecMul (star (cy y)) (Hpk k ρ) ⟨0, by omega⟩
      else -(Matrix.vecMul (star (cy y)) (Hpk k ρ) ⬝ᵥ U.lowV k (j + 1) ρ z) := by
  have hw : (fun d => (XC x y).1 d 0) = cy y := by
    funext d
    simp [XC, CX]
  unfold U.Rn
  rw [ell_uni z hz, dif_pos (show 0 < j + 1 by omega)]
  by_cases hρ : 0 < ρ
  · rw [dif_pos hρ, dif_pos hρ, Matrix.neg_apply, wMat_mul_conjTranspose_mul_apply_last (XC x y).1 (Hpk k ρ) _ (by simp), hw]
  · rw [dif_neg hρ, dif_neg hρ, Matrix.neg_mulVec, Pi.neg_apply, neg_inj]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [wMat_mul_conjTranspose_mul_apply_last (XC x y).1 (Hpk k ρ) _ (by simp) c, hw]

theorem linear_form_radical_rank_one (y : U.RC k 1 ρ) (z : Fin (2 * (1 + ρ) + k + 1) → ℂ) (hz : inWb k (1 + ρ) z) :
    ell k (1 + ρ) z (U.Rn k 1 ρ y) =
      if hρ : 0 < ρ then -Matrix.vecMul (star (cy y)) (Hpk k ρ) ⟨0, by omega⟩
      else -(Matrix.vecMul (star (cy y)) (Hpk k ρ) ⬝ᵥ U.lowV k 1 ρ z) := by
  have hw : (fun d => y.1 d 0) = cy y := rfl
  unfold U.Rn
  rw [ell_uni z hz, dif_pos (show 0 < 1 by omega)]
  by_cases hρ : 0 < ρ
  · rw [dif_pos hρ, dif_pos hρ, Matrix.neg_apply, wMat_mul_conjTranspose_mul_apply_last y.1 (Hpk k ρ) _ rfl, hw]
  · rw [dif_neg hρ, dif_neg hρ, Matrix.neg_mulVec, Pi.neg_apply, neg_inj]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [wMat_mul_conjTranspose_mul_apply_last y.1 (Hpk k ρ) _ rfl c, hw]

theorem hsv (k j ρ : ℕ) : j + 1 + ρ = j + (1 + ρ) := by
  omega

theorem lowV_lowV (z : Fin (2 * (j + 1 + ρ) + k + 1) → ℂ) :
    U.lowV k 1 ρ (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) z)) = U.lowV k (j + 1) ρ z := by
  funext i
  simp only [U.lowV, D.castV]
  congr 1
  ext
  simp only [Fin.coe_cast]
  omega

theorem psi_eq_of_ell {r r' : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r)
    (g' : B.Mat k r') (h : ell k r z g = ell k r' z' g') : psi k r z cStd g = psi k r' z' cStd g' := by
  simp only [Formalism.QuantumDeterminants.psi, h]

theorem psiA (x : U.RC k j (1 + ρ)) (z : Fin (2 * (j + (1 + ρ)) + k + 1) → ℂ) (hz : inWb k (j + (1 + ρ)) z) :
    G.psi U.betaU (U.cornerA (aC x)) = psi k (j + (1 + ρ)) z cStd (U.Rn k j (1 + ρ) x) := by
  unfold Formalism.QuantumDeterminants.psi
  rw [ell_Rj x z hz]
  simp only [G.psi, U.cornerA, aC, U.betaU, Formalism.QuantumDeterminants.cStd]
  by_cases hj : 0 < j
  · rw [dif_pos (⟨by omega, hj⟩ : 0 < 1 ∧ 0 < j), dif_pos hj]
    rw [show (⟨j - 1, by omega⟩ : Fin j).rev = ⟨0, hj⟩ from Fin.ext (by simp [Fin.val_rev] <;> omega)]
    congr 3
    simp [Complex.mul_re] <;> ring
  · rw [dif_neg (fun h : 0 < 1 ∧ 0 < j => hj h.2), dif_neg hj]
    simp

theorem psiB (x : U.RC k j (1 + ρ)) (z : Fin (2 * (j + (1 + ρ)) + k + 1) → ℂ) (hz : inWb k (j + (1 + ρ)) z) :
    G.psi U.betaU (U.cornerB (bC x)) = star (psi k (j + (1 + ρ)) z cStd (U.Rn k j (1 + ρ) x)) := by
  unfold Formalism.QuantumDeterminants.psi
  rw [ell_Rj x z hz]
  simp only [G.psi, U.cornerB, bC, U.betaU, Formalism.QuantumDeterminants.cStd, Complex.star_def]
  by_cases hj : 0 < j
  · rw [dif_pos (⟨by omega, hj⟩ : 0 < 1 ∧ 0 < j), dif_pos hj]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, aC]
    rw [show (⟨j - 1, by omega⟩ : Fin j).rev = ⟨0, hj⟩ from Fin.ext (by simp [Fin.val_rev] <;> omega)]
    rw [← Complex.exp_conj]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  · rw [dif_neg (fun h : 0 < 1 ∧ 0 < j => hj h.2), dif_neg hj]
    simp

end chars

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

variable {k j ρ : ℕ}

theorem lowV_inWb {j' ρ' : ℕ} (z : Fin (2 * (j' + ρ') + k + 1) → ℂ) (hz : inWb k (j' + ρ') z) :
    inWb k ρ' (U.lowV k j' ρ' z) := by
  unfold Formalism.QuantumDeterminants.inWb at hz ⊢
  intro i hi
  apply hz
  show j' + i.val < j' + ρ' ∨ j' + ρ' + k < j' + i.val
  omega

theorem gpsi_add (β u v : ℂ) : G.psi β (u + v) = G.psi β u * G.psi β v := by
  simp only [G.psi, mul_add, Complex.add_re, Complex.ofReal_add]
  rw [← Complex.exp_add]

theorem PS (σ : Equiv.Perm (Fin j)) (zA zA' : Fin (2 * (j + 1 + ρ) + k + 1) → ℂ) (hzA : inWb k (j + 1 + ρ) zA)
    (hzA' : inWb k (j + 1 + ρ) zA') (x x' : U.RC k j (1 + ρ)) (η : U.XiH j 0 σ) (y y' : U.RC k 1 ρ) :
    U.psiStar (p := j) (s := 1) k ρ σ zA zA' ((XC x y, XC x' y'), ((aC x, bC x'), η.2)) =
      (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA)) cStd (U.Rn k 1 ρ y) *
        star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA')) cStd (U.Rn k 1 ρ y'))) *
      U.psiStar (p := j) (s := 0) k (1 + ρ) σ (D.castV (hsv k j ρ) zA) (D.castV (hsv k j ρ) zA') ((x, x'), η) := by
  have hc : inWb k (j + (1 + ρ)) (D.castV (hsv k j ρ) zA) := by
    unfold Formalism.QuantumDeterminants.inWb at hzA ⊢
    intro i hi
    simp only [D.castV]
    exact hzA _ (by simp only [Fin.coe_cast]; omega)
  have hc' : inWb k (j + (1 + ρ)) (D.castV (hsv k j ρ) zA') := by
    unfold Formalism.QuantumDeterminants.inWb at hzA' ⊢
    intro i hi
    simp only [D.castV]
    exact hzA' _ (by simp only [Fin.coe_cast]; omega)
  have e1 : psi k (j + 1 + ρ) zA cStd (U.Rn k (j + 1) ρ (XC x y)) =
      psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA)) cStd (U.Rn k 1 ρ y) := by
    apply psi_eq_of_ell
    rw [ell_RX x y zA hzA, linear_form_radical_rank_one y _ (lowV_inWb _ hc), lowV_lowV]
  have e2 : psi k (j + 1 + ρ) zA' cStd (U.Rn k (j + 1) ρ (XC x' y')) =
      psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA')) cStd (U.Rn k 1 ρ y') := by
    apply psi_eq_of_ell
    rw [ell_RX x' y' zA' hzA', linear_form_radical_rank_one y' _ (lowV_inWb _ hc'), lowV_lowV]
  have eA : G.psi U.betaU (U.cornerA (aC x)) =
      psi k (j + 0 + (1 + ρ)) (D.castV (hsv k j ρ) zA) cStd (U.Rn k (j + 0) (1 + ρ) x) := psiA x _ hc
  have eB : G.psi U.betaU (U.cornerB (bC x')) =
      star (psi k (j + 0 + (1 + ρ)) (D.castV (hsv k j ρ) zA') cStd (U.Rn k (j + 0) (1 + ρ) x')) := psiB x' _ hc'
  have h0A : U.cornerA η.1.1 = 0 := by simp [U.cornerA]
  have h0B : U.cornerB η.1.2 = 0 := by simp [U.cornerB]
  have eH : U.psiH (p := j) (s := 1) U.betaU σ ((aC x, bC x'), η.2) =
      U.psiH (p := j) (s := 0) U.betaU σ η * G.psi U.betaU (U.cornerA (aC x)) *
        G.psi U.betaU (U.cornerB (bC x')) := by
    simp only [U.psiH, h0A, h0B, add_zero, gpsi_add]
    try ring
  simp only [U.psiStar]
  rw [e1, e2, eH, eA, eB]
  ring

end Formalism.FourierDecayAlt.P.PBH
