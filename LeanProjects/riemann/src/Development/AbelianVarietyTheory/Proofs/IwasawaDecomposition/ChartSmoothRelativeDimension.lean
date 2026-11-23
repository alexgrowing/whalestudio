import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRelativeDimOfTrdegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartResidueTrdegGenericStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartResidueTrdegEqStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

namespace GlobalTheory.LocM.FullFlagDim

theorem smoothOfRelativeDimension_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : Mdl Y i₀), (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ (a : Fin Z.m) (g : Sp Γ(Z.X, (Z.U a).1) ⟶ (Xo Z.i.l).XF Z.i.c), g ≫ (Y Z.i).j = Z.chart a ≫ Z.π → SmoothOfRelativeDimension (∑ τ : E →+* ℂ, (Dw.mult τ).choose 2) g := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z hfull a g hg
  have hj : IsOpenImmersion (Y Z.i).j := GlobalTheory.TriplesAlong.isOpenImmersion_j W (Y Z.i)
  have hc : SmoothOfRelativeDimension (∑ τ : E →+* ℂ, (Dw.mult τ).choose 2) (Z.chart a ≫ Z.π) :=
    GlobalTheory.T.smooth_relative_dim_of_trdeg (Z.chart a ≫ Z.π) _ (Z.smooth a) fun x hx =>
      le_antisymm (GlobalTheory.T.chart_residue_trdeg_eq Z hfull a x) (GlobalTheory.T.chart_residue_trdeg_generic Z hfull a x hx)
  have hr : Set.range (Z.chart a ≫ Z.π) ⊆ Set.range (Y Z.i).j := by
    rintro _ ⟨x, rfl⟩
    rw [← hg]
    exact ⟨g x, by simp⟩
  have hl : IsOpenImmersion.lift (Y Z.i).j (Z.chart a ≫ Z.π) hr = g := by
    rw [← cancel_mono (Y Z.i).j, IsOpenImmersion.lift_fac, hg]
  rw [← hl]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (IsOpenImmersion.isPullback_lift_id _ _ hr).flip hc

end GlobalTheory.LocM.FullFlagDim
