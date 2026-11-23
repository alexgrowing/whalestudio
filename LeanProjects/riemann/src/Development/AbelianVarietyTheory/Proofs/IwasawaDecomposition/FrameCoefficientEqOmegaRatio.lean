import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChangeImports
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpFourClauses
import Formalism.LocalToGlobal.ProjectiveLattices.OpenRowsFree
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FramePairGram

theorem coef_conj_eq_coOm {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (τ : X.Ψ)
    (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) :
    (Matrix.of fun b i : Fin (r - j) => coef X x x' (conjEmb τ.1) b i) =
      (((coOm X hj x τ)⁻¹ * coOm X hj x' τ)ᵀ).submatrix Fin.rev Fin.rev := by
  have hd0 : IsUnit (mat (x0F X) τ).det := (det_x0F X τ).isUnit
  have hd : IsUnit (mat x τ).det := (hx τ).1.isUnit
  have hf : IsUnit (frameCo X hj x τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ hd0).mul hd
  have hN : (frameCo X hj x τ)⁻¹ * frameCo X hj x' τ =
      reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
    simp only [frameCo, inv_reindex]
    simp only [reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hd0, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd0]
  have h12 : (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₁₂ = 0 := by
    ext a c
    simp only [toBlocks₁₂, of_apply, reindex_apply, submatrix_apply, Matrix.zero_apply]
    apply PointWell.block_of_moeb_eq X hj hp hx hx' τ h
    · rw [idx_symm_inl, hp]; omega
    · rw [idx_symm_inr, hp]; exact c.2
  have hO : (coOm X hj x τ)⁻¹ * coOm X hj x' τ =
      (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₂₂ := by
    have e : frameCo X hj x' τ = frameCo X hj x τ * reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
      rw [← hN, mul_nonsing_inv_cancel_left _ _ hf]
    have e2 : coOm X hj x' τ = coOm X hj x τ * (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₂₂ := by
      rw [coOm, coOm, e]
      conv_lhs => rw [← fromBlocks_toBlocks (frameCo X hj x τ),
        ← fromBlocks_toBlocks (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)), fromBlocks_multiply,
        toBlocks_fromBlocks₂₂]
      rw [h12, Matrix.mul_zero, zero_add]
    rw [e2, ← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_coOm X hj hp hx τ), Matrix.one_mul]
  have cc : conjEmb (conjEmb τ.1) = τ.1 := RingHom.ext fun a => by simp [conjEmb]
  have hcc : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [cc]; exact τ.2
  have hc : conjEmb τ.1 ∉ X.Ψ := fun hc => ((X.cmType τ.1).mp τ.2) hc
  have hs : (⟨conjEmb (conjEmb τ.1), hcc⟩ : X.Ψ) = τ := Subtype.ext cc
  rw [hO]
  ext b i
  have hb := b.2
  have hi := i.2
  have hl : X.p0 - 1 - (i : ℕ) < r ∧ X.p0 - 1 - (b : ℕ) < r := by omega
  simp only [of_apply, submatrix_apply, transpose_apply, coef, dif_neg hc, dif_pos hcc, ent, dif_pos hl, hs,
    toBlocks₂₂, reindex_apply]
  refine congrArg₂ _ (Fin.ext ?_) (Fin.ext ?_) <;> simp [idx_symm_inr, Fin.val_rev, hp] <;> omega

end GlobalTheory.FramePairGram
