import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeContinuousFamily
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenframe_continuous_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (σ : c.F →+* ℂ) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (T : Type) [TopologicalSpace T] (a : T → CxFr Z σ) (S : Set T), ContinuousOn (fun t => (a t).1) S → (∀ t ∈ S, ∃ hy : (a t).1 ∈ ptsIn (genStr Z) σ V.1, F.IsMap (evHom hy) (a t).2) → ∀ τ : E →+* ℂ, ContinuousOn (fun t => x.gram (a t).1 (a t).2 τ) S := by
  first | exact @GlobalTheory.ShFam.OddPrimesWithRootsOfUnity.gram_continuousOn_baseChange | exact GlobalTheory.ShFam.OddPrimesWithRootsOfUnity.gram_continuousOn_baseChange | (intros; apply GlobalTheory.ShFam.OddPrimesWithRootsOfUnity.gram_continuousOn_baseChange <;> assumption)
