import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

private theorem herm_mulVec_mulVec' {g : ℕ} (H0 H1 B : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ z w, hermForm H1 (B *ᵥ z) (B *ᵥ w) = hermForm H0 z w) :
    H0 = Bᵀ * H1 * B.map conj := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have hs : star (Pi.single j 1 : Fin g → ℂ) = (Pi.single j 1 : Fin g → ℂ) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have e : hermForm H0 (Pi.single i 1) (Pi.single j 1) = H0 i j := by
    unfold hermForm
    rw [hs]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e] at h1
  rw [← h1]
  simp [hermForm, Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply, Finset.mul_sum,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm)

theorem det_hx_of_isUnitFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, IsUnitFr X x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ z w, hermForm Hm z w = hx X bas idx x z w) → Hm.det = ((∏ τ : X.Ψ, X.c τ ^ r : ℝ) : ℂ) := by
  intro E _ _ _ r X g bas idx n hs hn x hx hu Hm hH
  have hG : ∀ a b, cc (X.Gm a b) = X.Gm b a := X.4
  have hA : x ∈ GG X.Ψ X.Gm X.p0 := by
    unfold Data.dom at hx
    exact hx
  obtain ⟨x₀, b, hb, ho, hbd, rfl⟩ :=
    (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm hG).1 x hA hu
  have ho' : X.IsOrtho x₀ := ho

  have hone : (1 : Matrix (Fin g) (Fin g) ℂ).map conj = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have h1 : Hm = GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b) := by
    have h := herm_mulVec_mulVec' Hm (GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b)) 1 (by
      intro z w
      rw [Matrix.one_mulVec, Matrix.one_mulVec, hH, GlobalTheory.ThFr.hermForm_Hm]
      rfl)
    rw [h, hone, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

  have h0 : GlobalTheory.ThFr.Hm X bas idx x₀ = ((GlobalTheory.ThFr.borMat X b).submatrix idx idx)ᵀ *
      GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b) * ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).map conj :=
    herm_mulVec_mulVec' _ _ _ (fun z w =>
      GlobalTheory.ThFr.hermForm_Hm_rmul (bas := bas) (idx := idx) (x := x₀) (hb := hb) z w)
  have hdet0 := GlobalTheory.ThFr.det_Hm_of_isOrtho (idx := idx) (hs := hs) (ho := ho')
  have hnB : ‖((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det‖ = 1 := by
    rw [GlobalTheory.ThFr.det_borMat hb idx, norm_prod]
    apply Finset.prod_eq_one
    intro p _
    unfold GlobalTheory.ThFr.rowFac
    split_ifs <;> simp [hbd]
  have hc : (((GlobalTheory.ThFr.borMat X b).submatrix idx idx).map conj).det =
      conj ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det := by
    rw [RingHom.map_det]
    rfl
  have hm : ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det *
      conj ((GlobalTheory.ThFr.borMat X b).submatrix idx idx).det = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnB]
    norm_num
  rw [h1, ← hdet0, h0, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]
  linear_combination (-(GlobalTheory.ThFr.Hm X bas idx (rmul x₀ b)).det) * hm

end GlobalTheory.Dict
