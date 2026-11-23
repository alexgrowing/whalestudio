import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Ux5

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

lemma inv_eq_hpk {k r : ℕ} (n : B.Mat k r) (hu : nᴴ * Hpk k r * n = Hpk k r) :
    n⁻¹ = Hpk k r * nᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc nᴴ, hu, Formalism.QuantumDeterminants.GBasic.Hpk_sq]

lemma EB_inv_hpk {k r : ℕ} (n : B.Mat k r) (hu : nᴴ * Hpk k r * n = Hpk k r) :
    EB n⁻¹ (((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * B.gN n) := by
  rw [inv_eq_hpk n hu]
  have h1 : EB nᴴ (B.gN n) := EB_conjTranspose fun i j => entry_le_gN n i j
  have h2 := EB_mulF (EB_mulF (EB_Hpk k r) h1) (EB_Hpk k r)
  refine h2.mono (le_of_eq ?_)
  ring

lemma one_le_gN_sq {k r : ℕ} (n : B.Mat k r) (hu : nᴴ * Hpk k r * n = Hpk k r) :
    1 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 * B.gN n ^ 2 := by
  have hinv : n⁻¹ * n = 1 := by
    rw [inv_eq_hpk n hu, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc nᴴ, hu, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have h := EB_mulF (EB_inv_hpk n hu) (fun i j => entry_le_gN n i j)
  have i0 : Fin (2 * r + k + 1) := ⟨0, by omega⟩
  have := h i0 i0
  rw [hinv, Matrix.one_apply_eq, norm_one] at this
  refine this.trans (le_of_eq ?_)
  ring

lemma lsz_conj_le {k r : ℕ} (n M : B.Mat k r) (hu : nᴴ * Hpk k r * n = Hpk k r) {c : ℝ} (hM : EB M c)
    (hc : 0 ≤ c) :
    lsz (n⁻¹ * M * n) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 4 * (1 + c) * B.gN n ^ 2 := by
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)
  have hN : 1 ≤ N := Nat.one_le_cast.mpr (by omega)
  have hg : 0 ≤ B.gN n := Real.sqrt_nonneg _
  have h := EB_mulF (EB_mulF (EB_inv_hpk n hu) hM) (fun i j => entry_le_gN n i j)
  have hmx : mx (n⁻¹ * M * n) ≤ N ^ 4 * c * B.gN n ^ 2 := by
    refine mx_le (h.mono (le_of_eq (by simp only [N]; ring))) (by positivity)
  have h1 : 1 ≤ N ^ 3 * B.gN n ^ 2 := one_le_gN_sq n hu
  have h3 : N ^ 3 ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
  have h4 : 0 ≤ B.gN n ^ 2 := sq_nonneg _
  have h5 : N ^ 3 * B.gN n ^ 2 ≤ N ^ 4 * B.gN n ^ 2 := mul_le_mul_of_nonneg_right h3 h4
  have h6 : 0 ≤ N ^ 4 * B.gN n ^ 2 * c := by positivity
  unfold lsz
  refine max_le ?_ ?_
  · nlinarith
  · nlinarith

lemma EB_hat {k j ρ : ℕ} (Y : B.Mat k ρ) {c : ℝ} (hY : EB Y c) (hc : 0 ≤ c) :
    EB (blk3 (0 : Matrix (Fin j) (Fin j) ℂ) 0 0 0 Y 0 0 0 0 : B.Mat k (j + ρ)) c := by
  unfold EB blk3 at *
  intro a b
  show ‖fromBlocks (fromBlocks 0 0 0 Y) (fromRows 0 0) (fromCols 0 0) 0
    ((eB k j ρ).symm a) ((eB k j ρ).symm b)‖ ≤ c
  rcases (eB k j ρ).symm a with (a' | a') | a' <;> rcases (eB k j ρ).symm b with (b' | b') | b' <;>
    simp [hc, hY]

theorem letterSize : LetterSize := by
  intro k j ρ
  refine ⟨((2 * (j + ρ) + k + 1 : ℕ) : ℝ) ^ 4 * (1 + 1), fun x Y hY => ?_⟩
  have hb : EB (blk3 (0 : Matrix (Fin j) (Fin j) ℂ) 0 0 0 Y 0 0 0 0 : B.Mat k (j + ρ)) 1 := EB_hat Y hY zero_le_one
  exact lsz_conj_le (Rn k j ρ x) _ (Formalism.FourierDecayAlt.P.Ux4.Rn_unitary x) hb zero_le_one

lemma entry_bound_block_matrix_two {p s : ℕ} {A : Matrix (Fin p) (Fin p) ℂ} {B' : Matrix (Fin p) (Fin s) ℂ}
    {C' : Matrix (Fin s) (Fin p) ℂ} {D : Matrix (Fin s) (Fin s) ℂ} {c : ℝ}
    (hA : EB A c) (hB : EB B' c) (hC : EB C' c) (hD : EB D c) : EB (blk2 A B' C' D) c := by
  intro i j
  show ‖fromBlocks A B' C' D (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)‖ ≤ c
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b
  · exact hA a b
  · exact hB a b
  · exact hC a b
  · exact hD a b

lemma block_matrix_two_unipotent_inv {p s : ℕ} (b : Matrix (Fin p) (Fin s) ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) b 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ = blk2 1 (-b) 0 1 := by
  apply Matrix.inv_eq_left_inv
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

lemma EB_eMat {s : ℕ} (a b : Fin s) (ε : Bool) : EB (eMat a b ε) 1 := by
  unfold EB eMat
  intro i j
  simp only [Matrix.of_apply]
  split_ifs <;> simp

lemma EB_of_pi {p s : ℕ} (b : Fin p → Fin s → ℂ) : EB (Matrix.of b) (1 + ‖b‖) := by
  intro i j
  simp only [Matrix.of_apply]
  exact ((norm_le_pi_norm (b i) j).trans (norm_le_pi_norm b i)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem dirSize : DirSize := by
  intro hD k p s ρ σ
  refine ⟨((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) ^ 4 *
    (1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * ((p + s : ℕ) : ℝ) ^ 2), fun ξ i => ⟨?_, ?_⟩⟩
  · unfold dirZ dmuP
    exact (hD k (p + s) ρ ξ.1.2).2 _
  · have ht : 1 ≤ 1 + ‖ξ.2.1.2‖ := by linarith [norm_nonneg ξ.2.1.2]
    have h0 : (0 : ℝ) ≤ 1 + ‖ξ.2.1.2‖ := by linarith
    have hb := EB_of_pi ξ.2.1.2
    have hU : EB (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))
        (1 + ‖ξ.2.1.2‖) :=
      entry_bound_block_matrix_two (EB_one.mono ht) hb (EB_zero.mono h0) (EB_one.mono ht)
    have hUi : EB (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹
        (1 + ‖ξ.2.1.2‖) := by
      rw [block_matrix_two_unipotent_inv]
      exact entry_bound_block_matrix_two (EB_one.mono ht) (EB_neg hb) (EB_zero.mono h0) (EB_one.mono ht)
    have hE : EB (blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (eMat i.1 i.2.1 i.2.2)) 1 :=
      entry_bound_block_matrix_two (EB_zero.mono zero_le_one) (EB_zero.mono zero_le_one) (EB_zero.mono zero_le_one)
        (EB_eMat _ _ _)
    have hQ := EB_mulF (EB_mulF hUi hE) hU
    have hW := EB_mulF (EB_mulF (EB_wMat (p + s)) (EB_conjTranspose hQ)) (EB_wMat (p + s))
    have hJ : (0 : ℝ) ≤ ((p + s : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcQ : (0 : ℝ) ≤ ((p + s : ℕ) : ℝ) * (((p + s : ℕ) : ℝ) * ((1 + ‖ξ.2.1.2‖) * 1) * (1 + ‖ξ.2.1.2‖)) := by
      positivity
    have hc1 : ((p + s : ℕ) : ℝ) * (((p + s : ℕ) : ℝ) * ((1 + ‖ξ.2.1.2‖) * 1) * (1 + ‖ξ.2.1.2‖)) ≤
        (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) := by
      have : (0 : ℝ) ≤ ((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2 := by positivity
      nlinarith
    have hc2 : ((p + s : ℕ) : ℝ) * (((p + s : ℕ) : ℝ) * (1 * (((p + s : ℕ) : ℝ) * (((p + s : ℕ) : ℝ) * ((1 + ‖ξ.2.1.2‖) * 1) * (1 + ‖ξ.2.1.2‖)))) * 1) ≤
        (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) := by
      have : (0 : ℝ) ≤ ((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2 := by positivity
      nlinarith
    have hc : (0 : ℝ) ≤ (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) := by
      positivity
    have hM := entry_bound_block3 (k := k) (ρ := ρ) (hQ.mono hc1) (EB_zero.mono hc) (EB_zero.mono hc) (EB_zero.mono hc)
      (EB_zero.mono hc) (EB_zero.mono hc) (EB_zero.mono hc) (EB_zero.mono hc) (EB_neg (hW.mono hc2))
    have key := lsz_conj_le (Rn k (p + s) ρ ξ.1.2) _ (Formalism.FourierDecayAlt.P.Ux4.Rn_unitary ξ.1.2) hM hc
    unfold dirZ dmuP
    refine key.trans ?_
    have hg : (0 : ℝ) ≤ ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) ^ 4 * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 := by
      positivity
    have ht2 : 1 ≤ (1 + ‖ξ.2.1.2‖) ^ 2 := one_le_pow₀ ht
    have hJ2 : (0 : ℝ) ≤ (((p + s : ℕ) : ℝ) ^ 2 + 1) * ((p + s : ℕ) : ℝ) ^ 2 := by positivity
    have hin : 1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) ≤
        (1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * ((p + s : ℕ) : ℝ) ^ 2) * (1 + ‖ξ.2.1.2‖) ^ 2 := by
      nlinarith
    calc ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) ^ 4 *
          (1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2)) *
          B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2
        = ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) ^ 4 * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 *
          (1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * (((p + s : ℕ) : ℝ) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2)) := by ring
      _ ≤ ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) ^ 4 * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 *
          ((1 + (((p + s : ℕ) : ℝ) ^ 2 + 1) * ((p + s : ℕ) : ℝ) ^ 2) * (1 + ‖ξ.2.1.2‖) ^ 2) :=
          mul_le_mul_of_nonneg_left hin hg
      _ = _ := by ring

end PI.UnitaryGroupMassFormula.UsCost
