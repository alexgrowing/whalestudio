import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder
open Matrix

namespace GlobalTheory.DualOrthSum

open GlobalTheory.HermFrame

theorem form_blockSum {m n : Type} [Fintype m] [Fintype n] (A : Matrix m m ℂ)
    (B : Matrix n n ℂ) (x y : m ⊕ n → ℂ) :
    form (fromBlocks A 0 0 B) x y =
      form A (x ∘ Sum.inl) (y ∘ Sum.inl) + form B (x ∘ Sum.inr) (y ∘ Sum.inr) := by
  simp [form_eq_sum, Fintype.sum_sum_type]

theorem dualGram_fromBlocks_diag {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : IsUnit A.det) (hB : IsUnit B.det) :
    dualGram (fromBlocks A 0 0 B) = fromBlocks (dualGram A) 0 0 (dualGram B) := by
  have : (fromBlocks A 0 0 B)⁻¹ = fromBlocks A⁻¹ 0 0 B⁻¹ := Matrix.inv_eq_right_inv (by
    simp [fromBlocks_multiply, Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hB])
  simp [dualGram, this, fromBlocks_transpose]

theorem form_dualGram_submatrix {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (e : m ≃ n) (H : Matrix n n ℂ) (u w : n → ℂ) :
    form (dualGram (H.submatrix e e)) (u ∘ e) (w ∘ e) = form (dualGram H) u w := by
  rw [dualGram, dualGram, inv_submatrix_equiv, form_eq_sum, form_eq_sum]
  refine Fintype.sum_equiv e _ _ fun i => Fintype.sum_equiv e _ _ fun j => ?_
  simp

theorem form_dualGram_chg_transpose {n : Type} [Fintype n] [DecidableEq n] {N : Matrix n n ℂ}
    (hN : IsUnit N.det) (D : Matrix n n ℂ) (x y : n → ℂ) :
    form (dualGram (chg N D)) (Nᵀ *ᵥ x) (Nᵀ *ᵥ y) = form (dualGram D) x y := by
  have h := Matrix.mul_nonsing_inv N hN
  have h' : N⁻¹ᵀ * Nᵀ = 1 := by rw [← transpose_mul, h, transpose_one]
  rw [dualGram_chg h, form_chg, mulVec_mulVec, mulVec_mulVec, h', one_mulVec, one_mulVec]

theorem form_dualGram_orthSum : ∀ (g g₁ g₂ : ℕ), g = g₁ + g₂ → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (H₁ : Matrix (Fin g₁) (Fin g₁) ℂ) (H₂ : Matrix (Fin g₂) (Fin g₂) ℂ) (M₁ : Matrix (Fin g₁) (Fin g) ℂ) (M₂ : Matrix (Fin g₂) (Fin g) ℂ), H.PosDef → H₁.PosDef → H₂.PosDef → (∀ z w, HermFrame.form H z w = HermFrame.form H₁ (M₁.mulVec z) (M₁.mulVec w) + HermFrame.form H₂ (M₂.mulVec z) (M₂.mulVec w)) → ∀ (t : ℝ), 0 < t → ∀ (a a' : Fin g₁ → ℂ) (b b' : Fin g₂ → ℂ), HermFrame.form (HermFrame.dualGram ((t : ℂ) • H)) (M₁.transpose.mulVec a + M₂.transpose.mulVec b) (M₁.transpose.mulVec a' + M₂.transpose.mulVec b') = HermFrame.form (HermFrame.dualGram ((t : ℂ) • H₁)) a a' + HermFrame.form (HermFrame.dualGram ((t : ℂ) • H₂)) b b' := by
  intro g g₁ g₂ hg H H₁ H₂ M₁ M₂ hH hH₁ hH₂ hsum t ht a a' b b'
  have ht' : (0 : ℂ) < (t : ℂ) := by exact_mod_cast ht
  let e : Fin g₁ ⊕ Fin g₂ ≃ Fin g := finSumFinEquiv.trans (finCongr hg.symm)
  let M : Matrix (Fin g₁ ⊕ Fin g₂) (Fin g) ℂ := Matrix.fromRows M₁ M₂
  let N : Matrix (Fin g₁ ⊕ Fin g₂) (Fin g₁ ⊕ Fin g₂) ℂ := M.submatrix id e
  let D : Matrix (Fin g₁ ⊕ Fin g₂) (Fin g₁ ⊕ Fin g₂) ℂ :=
    fromBlocks ((t : ℂ) • H₁) 0 0 ((t : ℂ) • H₂)
  have hM : (t : ℂ) • H = chg M D := by
    ext i j
    rw [← form_single ((t : ℂ) • H), ← form_single (chg M D), form_chg, form_smul, hsum,
      form_blockSum, form_smul, form_smul, mul_add, fromRows_mulVec, fromRows_mulVec]
    rfl
  have hN : chg N D = ((t : ℂ) • H).submatrix e e := by
    rw [hM]
    ext i j
    rw [submatrix_apply, chg_apply, chg_apply]
    rfl
  have hdet : IsUnit N.det := by
    have h1 : (chg N D).det ≠ 0 := by
      rw [hN, det_submatrix_equiv_self]
      exact (hH.smul ht').det_pos.ne'
    rw [det_chg] at h1
    refine isUnit_iff_ne_zero.2 fun h0 => h1 ?_
    simp [h0]
  have hv (c : Fin g₁ → ℂ) (d : Fin g₂ → ℂ) :
      (M₁ᵀ *ᵥ c + M₂ᵀ *ᵥ d) ∘ e = Nᵀ *ᵥ Sum.elim c d := by
    funext i
    simp [N, M, mulVec, dotProduct, Fintype.sum_sum_type]
  rw [← form_dualGram_submatrix e, ← hN, hv, hv, form_dualGram_chg_transpose hdet,
    dualGram_fromBlocks_diag (hH₁.smul ht').det_pos.ne'.isUnit (hH₂.smul ht').det_pos.ne'.isUnit,
    form_blockSum]
  rfl

end GlobalTheory.DualOrthSum
