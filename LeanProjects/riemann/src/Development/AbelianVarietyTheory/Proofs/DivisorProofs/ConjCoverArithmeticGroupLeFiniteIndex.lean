import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjIsometryMovesCoverPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqArithmeticGroupMulScalarOfMovedFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverComparisonScalarEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIsometryFlagDomainGroupNeZeroStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

theorem goodEmb_comp_eF {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0)
    (σ₂ : d.c₂.F →+* ℂ) (h : GoodEmb d.c₂ σ₂) : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := by
  unfold GoodEmb at h ⊢
  rw [← h]
  rfl

theorem conj_arithGroup_le : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ((U₂ σ₂).X k₂).Γ.map (MulAut.conj δ).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj δ).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ≠ 0 := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hGm hδ hov
  have hσ := goodEmb_comp_eF d σ₂ hσ₂
  have hΨ : ((U₂ σ₂).X k₂).Ψ = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ := by
    ext τ
    rw [((hL₂.unf σ₂ hσ₂).2.1 k₂).2 τ, ((hL.unf _ hσ).2.1 k).2 τ]
  refine ⟨?_, GlobalTheory.T.relIndex_conj_isometry_flagDomainGroup_ne_zero _ _ δ hGm hδ⟩
  intro g hg
  obtain ⟨γ₂, hγ₂, rfl⟩ := Subgroup.mem_map.1 hg
  obtain ⟨γ, hγ, ζ, hζ⟩ := GlobalTheory.T.eq_arithmeticGroup_mul_scalar_of_moved_frames _ _ δ (MulAut.conj δ γ₂) hΨ
    (fun x hx x' hm => GlobalTheory.T.arithmeticGroup_conj_isometry_moves_cover_point D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hGm hδ hov γ₂ hγ₂ x hx x' hm)
  have h1 := GlobalTheory.T.coverComparison_scalar_eq_one D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hGm hδ hov γ₂ hγ₂ γ hγ ζ hζ
  have e : (MulAut.conj δ).toMonoidHom γ₂ = γ := by
    apply Units.ext
    show ((MulAut.conj δ γ₂ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = _
    rw [hζ, h1, mul_one]
  rw [e]
  exact hγ

end GlobalTheory.LevModel
