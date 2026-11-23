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

theorem coef_eq_coW_change {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (τ : X.Ψ)
    (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) :
    (Matrix.of fun b i : Fin j => coef X x x' τ.1 b i) = (coW X hj x' τ)⁻¹ * coW X hj x τ := by
  have hd' : IsUnit (mat x' τ).det := (hx' τ).1.isUnit
  have hN : frameCo X hj x τ = frameCo X hj x' τ * reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ) := by
    simp only [frameCo, reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd']
  have hu' := frameCo_isUnit₂₂ X hj hp hx' τ
  have hW : coW X hj x τ = coW X hj x' τ * (reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ)).toBlocks₁₁ := by
    unfold coW
    rw [h, hN, moeb_zero]
    generalize frameCo X hj x' τ = g at *
    generalize reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ) = N
    have e11 : (g * N).toBlocks₁₁ = g.toBlocks₁₁ * N.toBlocks₁₁ + g.toBlocks₁₂ * N.toBlocks₂₁ := by
      conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks N]
      rw [fromBlocks_multiply, toBlocks_fromBlocks₁₁]
    have e21 : (g * N).toBlocks₂₁ = g.toBlocks₂₁ * N.toBlocks₁₁ + g.toBlocks₂₂ * N.toBlocks₂₁ := by
      conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks N]
      rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    rw [e11, e21]
    simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hu']
    abel
  rw [hW, ← Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 ((isUnit_iff_isUnit_det _).2 (isUnit_coW X hj hp hx' τ))), Matrix.one_mul]
  ext b i
  have hb : X.p0 + (b : ℕ) < r := by have := b.2; have := X.p0_le; omega
  have hi : X.p0 + (i : ℕ) < r := by have := i.2; have := X.p0_le; omega
  have eb : (idx hj).symm (Sum.inl b) = ⟨X.p0 + b, hb⟩ := Fin.ext (by rw [idx_symm_inl]; show r - j + (b : ℕ) = X.p0 + b; omega)
  have ei : (idx hj).symm (Sum.inl i) = ⟨X.p0 + i, hi⟩ := Fin.ext (by rw [idx_symm_inl]; show r - j + (i : ℕ) = X.p0 + i; omega)
  simp only [of_apply, coef, dif_pos τ.2, ent, dif_pos (And.intro hb hi), Subtype.coe_eta, toBlocks₁₁, reindex_apply,
    submatrix_apply, eb, ei]

end GlobalTheory.FramePairGram
