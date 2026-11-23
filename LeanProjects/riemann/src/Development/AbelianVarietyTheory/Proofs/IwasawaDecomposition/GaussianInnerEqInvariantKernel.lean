import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

theorem kerAlg_exponent {P Q : ℕ} (B : Matrix (Fin P) (Fin Q) ℂ) (C : Matrix (Fin Q) (Fin P) ℂ)
    (h : IsUnit (1 - C * B).det) (a c : Fin P → ℂ) (b d s u : Fin Q → ℂ) :
    -(b ⬝ᵥ s) + -(d ⬝ᵥ u) + (a ⬝ᵥ (1 - B * C)⁻¹ *ᵥ c + d ⬝ᵥ (1 - C * B)⁻¹ *ᵥ b
      + a ⬝ᵥ ((1 - B * C)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - C * B)⁻¹ * C) *ᵥ c) =
    ((a + s ᵥ* C) ⬝ᵥ (c + B *ᵥ u) - s ⬝ᵥ u) -
      (a ᵥ* B + d - s ᵥ* (1 - C * B)) ⬝ᵥ (1 - C * B)⁻¹ *ᵥ (-(b + C *ᵥ c) + (1 - C * B) *ᵥ u) := by
  have h1 := Matrix.nonsing_inv_mul _ h
  have h2 := Matrix.mul_nonsing_inv _ h
  generalize (1 - C * B)⁻¹ = N at h1 h2 ⊢
  have h3 : C * B * N = N - 1 := by rw [← h2, Matrix.sub_mul, Matrix.one_mul, sub_sub_cancel]
  have h4 : N * (C * B) = N - 1 := by rw [← h1, Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel]
  have hM : (1 - B * C)⁻¹ = 1 + B * N * C := by
    apply Matrix.inv_eq_right_inv
    have : B * C * (B * N * C) = B * (C * B * N) * C := by simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, this, h3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_one]
    abel
  have hMB : (1 + B * N * C) * B = B * N := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, h4, Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [hM, hMB]
  have e1 : N *ᵥ (-(b + C *ᵥ c) + (1 - C * B) *ᵥ u) = u - N *ᵥ (b + C *ᵥ c) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_neg]; abel
  have e2 : (s ᵥ* (1 - C * B)) ⬝ᵥ N *ᵥ (b + C *ᵥ c) = s ⬝ᵥ (b + C *ᵥ c) := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e1, dotProduct_sub, sub_dotProduct _ _ (N *ᵥ _), e2]
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add, ← Matrix.dotProduct_mulVec, Matrix.mulVec_add,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, dotProduct_sub,
    dotProduct_comm b s]
  ring

theorem kerAlg_proj {P Q : ℕ} (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det)
    (h' : IsUnit Y'.toRows₂.det) :
    Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q =
      Matrix.fromRows (matA Y') 1 * (1 - (matA Y)ᴴ * matA Y')⁻¹ * Matrix.fromCols (-(matA Y)ᴴ) 1 := by
  have hH : IsUnit (Y.toRows₂ᴴ).det := by rw [Matrix.det_conjTranspose]; exact h.star
  have e0 : Yᴴ * Jm P Q * Y' = (-Y.toRows₂ᴴ) * (1 - (matA Y)ᴴ * matA Y') * Y'.toRows₂ := by
    rw [Matrix.neg_mul, Matrix.neg_mul, ← form_factor Y Y' h h', neg_neg]
  have e1 : Yᴴ * Jm P Q = (-Y.toRows₂ᴴ) * Matrix.fromCols (-(matA Y)ᴴ) 1 := by
    conv_lhs => rw [frame_eq Y h]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, baseY, Jm, Formalism.UG.Jpq,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.neg_mul,
      ← Matrix.mul_neg]
    congr 1
    ext i (j | j) <;> simp
  have hN : IsUnit (-Y.toRows₂ᴴ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det] at hH ⊢; exact hH.neg
  rw [e0, Matrix.mul_assoc _ Yᴴ, e1, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have e2 := frame_eq Y' h'
  generalize matA Y' = B at e2 ⊢
  generalize Y'.toRows₂ = Z at e2 h' ⊢
  subst e2
  simp only [Matrix.mul_assoc, baseY]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ h', Matrix.nonsing_inv_mul_cancel_left _ _ hN]

theorem kerAlg : ∀ (P Q : ℕ) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v φ v' φ' : Ix P Q → ℂ), IsUnit Y.toRows₂.det → IsUnit Y'.toRows₂.det → IsUnit (1 - (matA Y)ᴴ * matA Y').det → let A := matA Y; let B := matA Y'; let a : Fin P → ℂ := fun i => star (linX Y v φ (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (linX Y v φ (Sum.inr j)); let c : Fin P → ℂ := fun i => linX Y' v' φ' (Sum.inl i); let d : Fin Q → ℂ := fun j => linX Y' v' φ' (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; star (scal Y v φ) * scal Y' v' φ' * (((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c)) = ker Y v φ Y' v' φ' := by
  intro P Q Y Y' v φ v' φ' h h' hK A B a b c d M N
  have hs : star (scal Y v φ) = ((Y.toRows₂ᴴ).det)⁻¹ * Complex.exp (-(b ⬝ᵥ star (v ∘ Sum.inr))) := by
    rw [scal, star_mul', star_inv₀, Matrix.det_conjTranspose, Complex.star_def, ← Complex.exp_conj]
    congr 2
    simp [b, dotProduct]
  have hs' : scal Y' v' φ' = (Y'.toRows₂.det)⁻¹ * Complex.exp (-(d ⬝ᵥ (v' ∘ Sum.inr))) := rfl
  have ha : star (v ∘ Sum.inl) = a + star (v ∘ Sum.inr) ᵥ* Aᴴ := by
    have : a = star (v ∘ Sum.inl - A *ᵥ (v ∘ Sum.inr)) := rfl
    rw [this, star_sub, Matrix.star_mulVec]; abel
  have hb : b = Aᴴ *ᵥ star (φ ∘ Sum.inl) + star (φ ∘ Sum.inr) := by
    have : b = star ((φ ∘ Sum.inl) ᵥ* A + φ ∘ Sum.inr) := rfl
    rw [this, star_add, Matrix.star_vecMul]
  have hc : v' ∘ Sum.inl = c + B *ᵥ (v' ∘ Sum.inr) := by
    have : c = v' ∘ Sum.inl - B *ᵥ (v' ∘ Sum.inr) := rfl
    rw [this]; abel
  have hd : d = (φ' ∘ Sum.inl) ᵥ* B + φ' ∘ Sum.inr := rfl
  have hJ1 : star v ᵥ* Jm P Q = Sum.elim (star (v ∘ Sum.inl)) (-star (v ∘ Sum.inr)) := by
    rw [Jm, Formalism.UG.Jpq, Matrix.vecMul_fromBlocks]
    ext (i | i) <;> simp [Matrix.vecMul_neg]
  have hJ2 : Jm P Q *ᵥ star φ = Sum.elim (star (φ ∘ Sum.inl)) (-star (φ ∘ Sum.inr)) := by
    rw [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_mulVec]
    ext (i | i) <;> simp [Matrix.neg_mulVec]
  have e0 : (star v ᵥ* Jm P Q) ⬝ᵥ v' = (a + star (v ∘ Sum.inr) ᵥ* Aᴴ) ⬝ᵥ (c + B *ᵥ (v' ∘ Sum.inr))
      - star (v ∘ Sum.inr) ⬝ᵥ (v' ∘ Sum.inr) := by
    rw [← ha, ← hc, hJ1]
    simp [dotProduct, Fintype.sum_sum_type, sub_eq_add_neg]
  have e1 : (star v ᵥ* Jm P Q + φ') ᵥ* Matrix.fromRows B 1 =
      a ᵥ* B + d - star (v ∘ Sum.inr) ᵥ* (1 - Aᴴ * B) := by
    have : star v ᵥ* Jm P Q + φ' = Sum.elim (star (v ∘ Sum.inl) + φ' ∘ Sum.inl)
        (-star (v ∘ Sum.inr) + φ' ∘ Sum.inr) := by
      rw [hJ1]; ext (i | i) <;> rfl
    rw [this, Matrix.sumElim_vecMul_fromRows, ha, hd]
    simp only [Matrix.add_vecMul, Matrix.vecMul_one, Matrix.vecMul_sub, Matrix.vecMul_vecMul]
    abel
  have e2 : Matrix.fromCols (-Aᴴ) 1 *ᵥ (Jm P Q *ᵥ star φ + v') =
      -(b + Aᴴ *ᵥ c) + (1 - Aᴴ * B) *ᵥ (v' ∘ Sum.inr) := by
    have : Jm P Q *ᵥ star φ + v' = Sum.elim (star (φ ∘ Sum.inl) + v' ∘ Sum.inl)
        (-star (φ ∘ Sum.inr) + v' ∘ Sum.inr) := by
      rw [hJ2]; ext (i | i) <;> rfl
    rw [this, Matrix.fromCols_mulVec_sumElim, hb]
    conv_lhs => rw [hc]
    simp only [Matrix.mulVec_add, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.neg_mulVec,
      Matrix.neg_mul]
    abel
  have key := kerAlg_exponent B Aᴴ hK a c b d (star (v ∘ Sum.inr)) (v' ∘ Sum.inr)
  rw [ker, kerAlg_proj Y Y' h h', form_factor Y Y' h h', ← Matrix.mulVec_mulVec _ (Matrix.fromRows _ _ * _),
    ← Matrix.mulVec_mulVec _ (Matrix.fromRows _ _), Matrix.dotProduct_mulVec _ (Matrix.fromRows _ _), e0, e1, e2,
    ← key, hs, hs', Complex.exp_add (-_ + -_), Complex.exp_add (-_) (-_), Matrix.det_mul, Matrix.det_mul]
  simp only [mul_inv, M, N, A, B]
  ring

end GlobalTheory.OscGauss

end
