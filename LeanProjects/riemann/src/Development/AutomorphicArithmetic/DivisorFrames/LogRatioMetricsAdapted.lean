import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolAdapted

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open Matrix GlobalTheory.GradedNorm GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.HodgeLogBd

private theorem hodge_log_bound_adapted {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {σ : F →+* ℂ}
    (G G₀ : EigMet Z (embOf e σ)) (n : Pad.Letter Dw → ℤ) (p : Y.Y.pts σ) (g : Y.FrameAt p)
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ} {t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℂˣ}
    (h2 : Y.Adapted p t g t') :
    lnRatio (C := cxSt F) (Y.met G n) (Y.met G₀ n) p =
      (∑ z : Pad.Letter Dw, (n z : ℝ) * (Real.log (grSq (G.gram _ g z.1) z.2) - Real.log (grSq (G₀.gram _ g z.1) z.2))) / 2 := by
  have hmem := FlagCpt.prodPow_mem n h2.mem_eqnSet
  have k1 := FlagCpt.met_h G n h2
  have k2 := FlagCpt.met_h G₀ n h2
  have hT : 0 < ‖((prodPow t' n : ℂˣ) : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.2 (Units.ne_zero _)) _
  have e1 : (cxSt F).pn Y.Y σ _ (Y.met G n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p =
      ‖GlobalTheory.ProjVar.Var.fval (prodPow t n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p‖ ^ 2 *
        (Y.genSq G n g / ‖((prodPow t' n : ℂˣ) : ℂ)‖ ^ 2) := by
    rw [← k1]; exact GlobalTheory.ProjVar.Var.pn_eq hmem
  have e2 : (cxSt F).pn Y.Y σ _ (Y.met G₀ n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p =
      ‖GlobalTheory.ProjVar.Var.fval (prodPow t n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p‖ ^ 2 *
        (Y.genSq G₀ n g / ‖((prodPow t' n : ℂˣ) : ℂ)‖ ^ 2) := by
    rw [← k2]; exact GlobalTheory.ProjVar.Var.pn_eq hmem
  have hP : PosAt (C := cxSt F) (Y.met G n) p := posAt_of_posSet (FlagCpt.posSet_met _ _) p
  have hg := Y.genSq_pos G n g
  have hg₀ := Y.genSq_pos G₀ n g
  have hK : 0 < ‖GlobalTheory.ProjVar.Var.fval (prodPow t n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p‖ ^ 2 := by
    have : 0 < (cxSt F).pn Y.Y σ _ (Y.met G n) ((cxSt F).cx Y.Y σ (genAt (Pad.divOf Y n) (under p))) p := hP
    rw [e1] at this
    exact pos_of_mul_pos_left this (div_pos hg hT).le
  simp only [lnRatio, lnN]
  rw [e1, e2, Real.log_mul hK.ne' (div_pos hg hT).ne', Real.log_mul hK.ne' (div_pos hg₀ hT).ne',
    Real.log_div hg.ne' hT.ne', Real.log_div hg₀.ne' hT.ne']
  have lg : ∀ G' : EigMet Z (embOf e σ), Real.log (Y.genSq G' n g) =
      ∑ z : Pad.Letter Dw, (n z : ℝ) * Real.log (grSq (G'.gram _ g z.1) z.2) := fun G' => by
    rw [FlagCpt.genSq, Real.log_prod (fun z _ => (zpow_pos (grSq_pos (G'.pos _ _ _) _) _).ne')]
    exact Finset.sum_congr rfl fun z _ => Real.log_zpow _ _
  rw [lg G, lg G₀]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end GlobalTheory.HodgeLogBd

end

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix
open scoped ComplexOrder
open GlobalTheory.ShFam.Hor GlobalTheory.HermFrame GlobalTheory.Toroidal

theorem UpperTheory.log_ratio_metrics_adapted :
    OnCore fun D O x P => ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ)) (g : ∀ p : GlobalTheory.CxPts (O.var c).str σ, (O.Φ.C c).FrameAt p), GlobalTheory.BdGram.IsHolAdapted O ch U g →
      ∀ y ∈ U, ∀ n : Letter O.S.Dw → ℤ, lnRatio (metsOf x O.Φ c none σ n) (refMet x O.Φ c σ n) y =
        (∑ z : Letter O.S.Dw, (n z : ℝ) * (Real.log (grSq (GlobalTheory.BdGram.gramIn O (x.hodge (embOf O.κ.e σ)) ch g z.1 (ch.e y)) z.2) - Real.log (grSq (GlobalTheory.BdGram.gramIn O (x.eigMet (embOf O.κ.e σ)) ch g z.1 (ch.e y)) z.2))) / 2 := by
  intro D O x P _ _ _ c σ ch U g hA y hy n
  obtain ⟨-, hU, -, hAd, -⟩ := hA
  obtain ⟨t, t', h⟩ := hAd y hy
  have hgram : ∀ (G : EigMet O.s.T.Z (embOf O.κ.e σ)) (τ : D.host.E →+* ℂ),
      GlobalTheory.BdGram.gramIn O G ch g τ (ch.e y) = G.gram _ (g y) τ := fun G τ => by
    unfold GlobalTheory.BdGram.gramIn
    rw [ch.e.left_inv (hU hy)]
  simp only [hgram]
  exact GlobalTheory.HodgeLogBd.hodge_log_bound_adapted (O.Φ.C c) (x.hodge (embOf O.κ.e σ)) (x.eigMet (embOf O.κ.e σ)) n y (g y) h
