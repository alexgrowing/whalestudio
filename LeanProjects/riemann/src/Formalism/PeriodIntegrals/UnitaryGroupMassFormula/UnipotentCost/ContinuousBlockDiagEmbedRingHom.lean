import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic

open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

section words

variable {k j ρ : ℕ}

def blockDiagEmbedRingHom (k j ρ : ℕ) : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ →+* B.Mat k (j + ρ) where
  toFun x := blk3 x.2 0 0 0 x.1 0 0 0 x.2
  map_one' := Formalism.FourierDecayAlt.P.Ux4.block3_one.symm
  map_mul' x y := by
    rw [Formalism.FourierDecayAlt.P.Ux4.block3_mul]
    simp
  map_zero' := Formalism.FourierDecayAlt.P.Ux4.block_three_zero_size_eq
  map_add' x y := by
    rw [Formalism.FourierDecayAlt.P.Ux4.block3_add]
    simp

theorem continuous_blockDiagEmbedRingHom : Continuous (blockDiagEmbedRingHom k j ρ) := by
  show Continuous (fun x : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ => blk3 x.2 0 0 0 x.1 0 0 0 x.2)
  simp only [blk3]
  exact ((continuous_snd.matrix_fromBlocks continuous_const continuous_const continuous_fst).matrix_fromBlocks
    continuous_const continuous_const continuous_snd).matrix_reindex _ _

theorem exp_pair (Y : B.Mat k ρ) :
    NormedSpace.exp ((Y, 0) : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ) = (NormedSpace.exp Y, 1) := by
  open scoped Norms.Operator in
  ext1
  · exact Prod.fst_exp _
  · exact (Prod.snd_exp _).trans NormedSpace.exp_zero

theorem embG_exp (Y : B.Mat k ρ) :
    embG k j ρ (NormedSpace.exp Y) = NormedSpace.exp (blk3 0 0 0 0 Y 0 0 0 0 : B.Mat k (j + ρ)) := by
  have h := (open scoped Norms.Operator in
    NormedSpace.map_exp (blockDiagEmbedRingHom k j ρ) continuous_blockDiagEmbedRingHom ((Y, 0) : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ))
  exact (congrArg (blockDiagEmbedRingHom k j ρ) (exp_pair (j := j) Y)).symm.trans h

theorem blockDiag3_smul_middle (c : ℂ) (Y : B.Mat k ρ) :
    (blk3 0 0 0 0 (c • Y) 0 0 0 0 : B.Mat k (j + ρ)) = c • blk3 0 0 0 0 Y 0 0 0 0 := by
  ext a b
  simp only [blk3, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  generalize (eB k j ρ).symm a = x
  generalize (eB k j ρ).symm b = y
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;> simp

theorem conj_exp {m : ℕ} (n X : Matrix (Fin m) (Fin m) ℂ) (hn : n * n⁻¹ = 1) :
    n⁻¹ * NormedSpace.exp X * n = NormedSpace.exp (n⁻¹ * X * n) :=
  (Matrix.exp_conj' n X ((Matrix.isUnit_iff_isUnit_det n).2 (Matrix.isUnit_det_of_right_inverse hn))).symm

private lemma Rn_mul_inv' (x : RC k j ρ) : Rn k j ρ x * (Rn k j ρ x)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  have h0 : (Matrix.fromCols (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ)) = 0 := by
    ext a b; rcases b with b | b <;> rfl
  simp only [Rn, blk3, Matrix.det_reindex_self]
  rw [h0, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem conj_letter (x : RC k j ρ) (Y : B.Mat k ρ) (c : ℂ) :
    (Rn k j ρ x)⁻¹ * embG k j ρ (NormedSpace.exp (c • Y)) * Rn k j ρ x =
      NormedSpace.exp (c • cj k j ρ x Y) := by
  rw [embG_exp, blockDiag3_smul_middle, conj_exp _ _ (Rn_mul_inv' x), Matrix.mul_smul, Matrix.smul_mul]
  rfl

end words

section comp

variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ} {ξ : Xi k p s ρ σ} {Z : G.Mat s}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdv_comp (hR : SliceRight) (H : B.Mat k (p + s + ρ) → E) (Y : B.Mat k ρ) :
    RdV Y (fun γ' => H (gaXi k ρ σ d ξ Z γ')) =
      fun γ' => RdV (cj k (p + s) ρ ξ.1.2 Y) H (gaXi k ρ σ d ξ Z γ') := by
  funext γ'
  simp only [RdV]
  congr 1
  funext t
  rw [hR k p s ρ σ d ξ Z γ' _, conj_letter]

theorem ldv_comp (hL : SliceLeft) (H : B.Mat k (p + s + ρ) → E) (Y : B.Mat k ρ) :
    B.LdV Y (fun γ' => H (gaXi k ρ σ d ξ Z γ')) =
      fun γ' => B.LdV (cj k (p + s) ρ ξ.1.1 Y) H (gaXi k ρ σ d ξ Z γ') := by
  funext γ'
  simp only [B.LdV]
  congr 1
  funext t
  rw [hL k p s ρ σ d ξ Z γ' _, ← neg_smul, conj_letter, neg_smul]

theorem rw_comp (hR : SliceRight) :
    ∀ (v : List (B.Mat k ρ)) (F : B.Mat k (p + s + ρ) → E),
      B.Rw v (fun γ' => F (gaXi k ρ σ d ξ Z γ')) =
        fun γ' => B.Rw (v.map (cj k (p + s) ρ ξ.1.2)) F (gaXi k ρ σ d ξ Z γ')
  | [], _ => rfl
  | Y :: v, F => by
    simp only [B.Rw, List.foldr_cons, List.map_cons] at *
    have ih := rw_comp hR v F
    simp only [B.Rw] at ih
    rw [ih]
    exact rdv_comp hR _ Y

theorem dLR_comp (hL : SliceLeft) (hR : SliceRight) (v : List (B.Mat k ρ)) (F : B.Mat k (p + s + ρ) → E) :
    ∀ u : List (B.Mat k ρ),
      B.dLR u v (fun γ' => F (gaXi k ρ σ d ξ Z γ')) =
        fun γ' => B.dLR (u.map (cj k (p + s) ρ ξ.1.1)) (v.map (cj k (p + s) ρ ξ.1.2)) F (gaXi k ρ σ d ξ Z γ')
  | [] => by
    simp only [B.dLR, List.foldr_nil, List.map_nil]
    exact rw_comp hR v F
  | Y :: u => by
    have ih := dLR_comp hL hR v F u
    simp only [B.dLR, List.foldr_cons, List.map_cons] at ih ⊢
    rw [ih]
    exact ldv_comp hL _ Y

end comp

theorem wordsId : WordsId := by
  intro hL hR k p s ρ σ d ξ Z E _ _ F u v
  exact dLR_comp hL hR v F u

end PI.UnitaryGroupMassFormula.UsCost
