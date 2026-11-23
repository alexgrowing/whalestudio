import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA

noncomputable section

namespace GlobalTheory.LevModel

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem exists_frBor_of_frOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {S : Type} [CommRing S] [Algebra c.F S]
    [Algebra d.c₂.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {p p' : FrPt d.Xo₂ d.c₂ S}
    (h : FrOver d p y) (h' : FrOver d p' y') (hb : FrBor t p p') : ∃ t' : Ix Dw → Sˣ, FrBor t' y y' := by
  obtain ⟨e, hu, -⟩ := h
  obtain ⟨e', hu', -⟩ := h'
  obtain ⟨ex, au, -⟩ := hb
  refine (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').2.1 (by rw [← e, ← e', ex]) fun τ i => ?_
  obtain ⟨cf, c₁, c₂, hcf⟩ := au τ i
  refine ⟨cf, by rw [c₁]; exact (t _).isUnit, c₂, ?_⟩
  have k := (GlobalTheory.FrameLift.comb_iff d.m e (fun j => (p.tan τ j).1) cf (ex ▸ (p'.tan τ i).1)).1 hcf
  rw [funext (hu τ), hu'] at k
  exact k

theorem lact_conj_eq_rmul : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ x ∈ ((U₂ σ₂).X k₂).dom, ∀ x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, GlobalTheory.LevModel.Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ x x' → ∃ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∃ b ∈ Bor ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, lact (MulAut.conj δ γ₂) x' = rmul (lact γ x') b := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hLev σ₂ hσ₂ k₂ k δ hG hδ hOv γ₂ hγ₂ x hx x' hM
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := by
    unfold GoodEmb at hσ₂ ⊢
    rw [← hσ₂]
    rfl
  have hU := hL.unf _ hσ
  have hU₂ := hL₂.unf _ hσ₂
  have hγx : lact γ₂ x ∈ ((U₂ σ₂).X k₂).dom := (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_mem_dom_iff _ hγ₂ x).2 hx
  obtain ⟨t₀, ht₀⟩ := (hU₂.2.2.2.1 k₂ k₂ ⟨x, hx⟩ ⟨lact γ₂ x, hγx⟩).2
    ⟨γ₂, hγ₂, ExtFPf.oneF _, ExtFPf.oneF_mem _, by rw [ExtFPf.rmul_oneF]⟩
  have hM' : Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ (lact γ₂ x) (lact (MulAut.conj δ γ₂) x') := by
    intro τ h₂ h₁
    have e := hM τ h₂ h₁
    show ((MulAut.conj δ γ₂ : GL _ _) : Matrix _ _ _).map τ * mat x' ⟨τ, h₁⟩ =
      (δ : Matrix _ _ _).map τ * ((γ₂ : Matrix _ _ _).map τ * mat x ⟨τ, h₂⟩)
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul (f := τ), ← Matrix.map_mul (f := τ),
      ← Units.val_mul, ← Units.val_mul, MulAut.conj_apply, inv_mul_cancel_right]
  obtain ⟨hx', t₁, -, y, hy₁, hy₂⟩ := hOv x hx x' hM
  obtain ⟨hx'', t₂, -, y', hy₁', hy₂'⟩ := hOv (lact γ₂ x) hγx _ hM'
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  obtain ⟨t', ht'⟩ := exists_frBor_of_frOver d hy₂ hy₂' ht₀
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ H Dw l Xo c (CAt σ₂)
  have hb := G.2.1 _ _ _ _ _ (G.2.1 _ _ _ _ _ hy₁ ht') (G.2.2.1 _ _ _ hy₁')
  obtain ⟨γ, hγ, b, hb', e⟩ := (hU.2.2.2.1 k k ⟨x', hx'⟩ ⟨_, hx''⟩).1 ⟨_, hb⟩
  exact ⟨γ, hγ, b, hb', eq_of_heq (Sigma.mk.inj e).2⟩

end GlobalTheory.LevModel
