import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelsDifferBySymplecticMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerPreservesSchwartzSpaceStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

namespace GlobalTheory.ModelChg

theorem det_ne_zero_of_hasSig {n r s : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : HasSig A r s) : A.det ≠ 0 := by
  obtain ⟨hrs, P, hP⟩ := h
  have hu : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) (0 : Matrix (Fin r) (Fin s) ℂ)
      (0 : Matrix (Fin s) (Fin r) ℂ) (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]; simp [Matrix.det_neg]
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 : (Pᵀ * A * P.map star).rank ≤ A.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [hP, h1] at h2
  simp at h2
  have h3 : A.rank = n := le_antisymm (by simpa using A.rank_le_card_width) (by omega)
  have h4 : LinearMap.range A.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h3)
  have h5 : Function.Surjective A.mulVec := LinearMap.range_eq_top.mp h4
  exact (Matrix.isUnit_iff_isUnit_det A |>.mp (Matrix.mulVec_surjective_iff_isUnit.mp h5)).ne_zero

theorem det_ne_zero_of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (B : Base F E) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ w, HasSig (c • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h1 := det_ne_zero_of_hasSig (h w)
  rw [Matrix.det_smul] at h1
  intro h0
  apply h1
  rw [show (J.map (B.emb w).1).det = (B.emb w).1 J.det from ((B.emb w).1.map_det J).symm, h0, map_zero, mul_zero]

theorem modelChange (hK : GlobalTheory.FunPr.Hypotheses₂) : GlobalTheory.ThK.ModelChange := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ om₁ hP₁
  obtain ⟨a, ha, hco⟩ := GlobalTheory.T.good_models_differ_by_symplectic_matrix F E σ B.ψ n d X W M M₁ hP.good hP₁.good
  obtain ⟨e, c, hc, hev, hbij, hθ⟩ :=
    GlobalTheory.T.symplectic_change_of_good_models_intertwines hK F E σ B n d X W M M₁ r s r' s' hP.base hP.herm hP.skew hP.good hP₁.good a ha hco
  obtain ⟨om₂, hW₂, hint⟩ := GlobalTheory.T.eigen_intertwiner_preserves_schwartz_space hK F E σ B n d X W M χX χW om r s r' s' hP M₁ hP₁.good e hev hbij
  have hX : X.J.det ≠ 0 :=
    det_ne_zero_of_sig B X.J 1 one_ne_zero (fun w => by simpa using hP.herm.sig w)
  have hWd : W.J.det ≠ 0 := det_ne_zero_of_sig B W.J Complex.I Complex.I_ne_zero hP.skew.sig
  have huniq := GlobalTheory.T.adelicWeilRep_schrodingerModel_unique F E σ hP.base.cm n d X W M₁ B.ψ χX χW hP.base.std hP.herm.herm hX
    hP.skew.skew hWd om₂ om₁ hW₂ hP₁.weil
  refine ⟨e, c, hc, hev, hbij, fun Φ hΦ => ⟨hθ Φ hΦ, fun x => ?_⟩⟩
  rw [hint x Φ hΦ, huniq x (e Φ) (hbij.mapsTo hΦ)]

end GlobalTheory.ModelChg
