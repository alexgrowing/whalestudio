import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartSmoothRelativeDimension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_smooth_relative_dimension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : Mdl Y i₀), (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ (a : Fin Z.m) (g : Sp Γ(Z.X, (Z.U a).1) ⟶ (Xo Z.i.l).XF Z.i.c), g ≫ (Y Z.i).j = Z.chart a ≫ Z.π → SmoothOfRelativeDimension (∑ τ : E →+* ℂ, (Dw.mult τ).choose 2) g := by
  first | exact @GlobalTheory.LocM.FullFlagDim.smoothOfRelativeDimension_lift | exact GlobalTheory.LocM.FullFlagDim.smoothOfRelativeDimension_lift | (intros; apply GlobalTheory.LocM.FullFlagDim.smoothOfRelativeDimension_lift <;> assumption)
