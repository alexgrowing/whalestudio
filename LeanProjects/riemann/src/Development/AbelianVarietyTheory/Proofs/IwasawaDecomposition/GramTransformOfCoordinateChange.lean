import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChangeImports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedFramesParabolicRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramePointCombinationMatrixStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoefficientEqWeightRatioStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoefficientEqOmegaRatioStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexOrder ContDiff

namespace GlobalTheory.FramePairGram

theorem gram_frames_eq : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s) (f f' : (s.fd k).dom), s.zOf L k f = s.zOf L k f' → ∀ t, (∀ T, coW (s.fd k) s.j_le f'.1 (s.lab L k t) * T = coW (s.fd k) s.j_le f.1 (s.lab L k t) → x.gramW L k f t = Tᴴ * x.gramW L k f' t * T) ∧ ∀ T, coOm (s.fd k) s.j_le f'.1 (s.lab L k t) * T = coOm (s.fd k) s.j_le f.1 (s.lab L k t) → x.gramOm L k f t = Tᴴ * x.gramOm L k f' t * T := by
  intro D A N j S κ s L k x f f' hz t
  have hp := s.p0_eq k
  have hmo : ∀ τ : (s.fd k).Ψ, moeb (frameCo (s.fd k) s.j_le f.1 τ) 0 = moeb (frameCo (s.fd k) s.j_le f'.1 τ) 0 := by
    intro τ
    obtain ⟨t', rfl⟩ := (s.lab L k).surjective τ
    exact congrFun hz t'
  have h1 := fun τ => PointWell.block_of_moeb_eq _ s.j_le hp f.2 f'.2 τ (hmo τ)
  have h2 := fun τ => PointWell.block_of_moeb_eq _ s.j_le hp f'.2 f.2 τ (hmo τ).symm
  have hx : ((s.U κ.σ₀).un k f).x = ((s.U κ.σ₀).un k f').x :=
    PointWell.pt_eq_of_block s.isUnf κ.good_σ₀ k f f' h1 h2
  have hg : ∀ τ, x.gram (s.framePt k f) (s.lieFrame k f) τ =
      (Matrix.of fun b i : Fin (S.Dw.mult τ) => coef (s.fd k) f.1 f'.1 τ b i)ᴴ *
        x.gram (s.framePt k f') (s.lieFrame k f') τ *
        Matrix.of fun b i : Fin (S.Dw.mult τ) => coef (s.fd k) f.1 f'.1 τ b i := fun τ =>
    GlobalTheory.T.frame_point_combination_matrix x _ _ hx τ _ (fun i => GlobalTheory.T.unfolded_frames_parabolic_relation s.isUnf κ.good_σ₀ k f f' h1 h2 τ i)
  constructor
  · intro T hT
    have hu := isUnit_coW (s.fd k) s.j_le hp f'.2 (s.lab L k t)
    have hT' : T = (coW (s.fd k) s.j_le f'.1 (s.lab L k t))⁻¹ * coW (s.fd k) s.j_le f.1 (s.lab L k t) := by
      rw [← hT, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [hT', ← GlobalTheory.T.frame_coefficient_eq_weight_ratio (s.fd k) s.j_le hp f.2 f'.2 (s.lab L k t) (hmo _)]
    unfold ToroidalCompactificationData.gramW
    rw [hg]
    set e := Fin.cast (S.mult_psi L t).symm
    have he : Function.Bijective e := (finCongr (S.mult_psi L t).symm).bijective
    rw [Matrix.submatrix_mul _ _ _ _ _ he, Matrix.submatrix_mul _ _ _ _ _ he, ← conjTranspose_submatrix]
    have hKe : (Matrix.of fun b i : Fin (S.Dw.mult (L.ψ t).1) => coef (s.fd k) f.1 f'.1 (L.ψ t).1 b i).submatrix e e =
        Matrix.of fun b i : Fin j => coef (s.fd k) f.1 f'.1 (s.lab L k t).1 b i := by
      ext b i; rfl
    rw [hKe]
  · intro T hT
    have hu := isUnit_coOm (s.fd k) s.j_le hp f'.2 (s.lab L k t)
    have hT' : T = (coOm (s.fd k) s.j_le f'.1 (s.lab L k t))⁻¹ * coOm (s.fd k) s.j_le f.1 (s.lab L k t) := by
      rw [← hT, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    have hK := GlobalTheory.T.frame_coefficient_eq_omega_ratio (s.fd k) s.j_le hp f.2 f'.2 (s.lab L k t) (hmo _)
    unfold ToroidalCompactificationData.gramOm
    rw [hg, dualGram_conj]
    set eo : Fin (N - j) ≃ Fin (S.Dw.mult (conjEmb (L.ψ t).1)) := Fin.revPerm.trans (finCongr (S.mult_conj L t).symm)
    have heo : (fun a : Fin (N - j) => Fin.cast (S.mult_conj L t).symm a.rev) = ⇑eo := rfl
    have key : ∀ (M G : Matrix (Fin (S.Dw.mult (conjEmb (L.ψ t).1))) (Fin (S.Dw.mult (conjEmb (L.ψ t).1))) ℂ),
        (Mᴴ * G * M).submatrix eo eo = (M.submatrix eo eo)ᴴ * G.submatrix eo eo * M.submatrix eo eo := by
      intro M G
      rw [Matrix.submatrix_mul _ _ _ _ _ eo.bijective, Matrix.submatrix_mul _ _ _ _ _ eo.bijective,
        ← conjTranspose_submatrix]
    have hu0 := isUnit_coOm (s.fd k) s.j_le hp f.2 (s.lab L k t)
    have hKo : ((Matrix.of fun b i : Fin (S.Dw.mult (conjEmb (L.ψ t).1)) =>
        coef (s.fd k) f.1 f'.1 (conjEmb (L.ψ t).1) b i)⁻¹ᵀ).submatrix eo eo = T := by
      have e1 : (Matrix.of fun b i : Fin (S.Dw.mult (conjEmb (L.ψ t).1)) =>
          coef (s.fd k) f.1 f'.1 (conjEmb (L.ψ t).1) b i).submatrix eo eo =
          ((coOm (s.fd k) s.j_le f.1 (s.lab L k t))⁻¹ * coOm (s.fd k) s.j_le f'.1 (s.lab L k t))ᵀ := by
        ext b i
        have := congrFun (congrFun hK b.rev) i.rev
        simp only [of_apply, submatrix_apply, Fin.rev_rev] at this
        exact Eq.trans rfl this
      rw [← transpose_submatrix, ← inv_submatrix_equiv, e1, transpose_nonsing_inv, transpose_transpose, hT',
        Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hu0]
    rw [heo, key, hKo, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.FramePairGram
