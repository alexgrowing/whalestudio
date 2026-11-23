import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricFlagCompactification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_metric_flag_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (G : EigMet Z (embOf e σ)) (T : Set (CxPts (genStr Z) (embOf e σ))), IsOpen T → G.SmoothOn (manifold Z (embOf e σ)) T → ∀ n : Pad.Letter Dw → ℤ, IsOpen (Y.down ⁻¹' T : Set (Y.Y.pts σ)) ∧ (Y.met G n).SmoothOn (Y.down ⁻¹' T) := by
  first | exact @GlobalTheory.ShFam.FlagCpt.smoothOn_met_of_eigMet | exact GlobalTheory.ShFam.FlagCpt.smoothOn_met_of_eigMet | (intros; apply GlobalTheory.ShFam.FlagCpt.smoothOn_met_of_eigMet <;> assumption)
