import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCoverArithmeticGroupLeFiniteIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentIndexSumEqConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverPullbackReadingEqUnitConstPowMulStatement

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevModel

theorem levCover_model : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∃ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E) (N : ℕ), 0 < N ∧ (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0) ∧ (∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N) ∧ ∃ t : (U₂ σ₂).Comp → ℂ, (∀ k₂, ‖t k₂‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → ∀ k₂ (x : Frame ((U₂ σ₂).X k₂).Ψ D.R.r) (x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ D.R.r), x ∈ ((U₂ σ₂).X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ) (h₁ : τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ), mat x' ⟨τ, h₁⟩ = (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → Even n → rdU (U₂ σ₂) g k₂ x = t k₂ ^ n * rdU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂) x' := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ
  have h1 := GlobalTheory.T.levelCover_component_over_base_rational_isometry D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ
  choose π δ hGm hIso hOv using h1
  have h2 := fun k₂ => GlobalTheory.T.conj_coverArithmeticGroup_le_finite_index D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ k₂ (π k₂) (δ k₂) (hGm k₂) (hIso k₂) (hOv k₂)
  obtain ⟨N, hN, hsum⟩ := GlobalTheory.T.levelCover_component_index_sum_eq_const D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ π δ
    (fun k₂ => ⟨hGm k₂, hIso k₂, (h2 k₂).1, (h2 k₂).2, hOv k₂⟩)
  have h4 := fun k₂ => GlobalTheory.T.levelCover_pullback_reading_eq_unitConst_pow_mul D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ k₂ (π k₂) (δ k₂) (hGm k₂) (hIso k₂) (hOv k₂)
  choose t ht hread using h4
  refine ⟨π, δ, N, hN, fun k₂ => ⟨hGm k₂, hIso k₂, (h2 k₂).1, (h2 k₂).2⟩, hsum, t, ht, ?_⟩
  intro a n hD f hf g hg hP k₂ x x' hx hm hn
  exact hread k₂ a n hD f hf g hg hP x x' hx hm hn

end GlobalTheory.LevModel
