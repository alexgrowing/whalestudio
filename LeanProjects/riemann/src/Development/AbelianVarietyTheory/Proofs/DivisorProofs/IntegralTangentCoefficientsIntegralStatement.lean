import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTangentCoefficientsIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_tangent_coefficients_integral : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (K : Type) [Field K] [NumberField K] (xO : Sp (𝓞 K) ⟶ X) (xK : Sp K ⟶ X) (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) (r : ℕ) (ε : Fin r → TanM xK t.G), IsCochFrame t xK ε → ∀ (a : Fin r → K) (w : TanM xO t.G), bcTan (algebraMap (𝓞 K) K) hx w = ∑ i, a i • ε i → ∀ i, a i ∈ Set.range (algebraMap (𝓞 K) K) := by
  first | exact @GlobalTheory.CochSat.cochar_saturated | exact GlobalTheory.CochSat.cochar_saturated | (intros; apply GlobalTheory.CochSat.cochar_saturated <;> assumption)
