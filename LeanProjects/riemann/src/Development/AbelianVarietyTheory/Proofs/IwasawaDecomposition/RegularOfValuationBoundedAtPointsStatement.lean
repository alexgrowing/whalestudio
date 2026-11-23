import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_of_valuation_bounded_at_points : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : TrueGeo.Model Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X → haveI := N.ar.isIntegral; ∀ (U : N.X.Opens) (f : N.X.functionField), (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X), spMap e.O.subtype ≫ yt = y.1 ≫ N.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (y.1 ≫ N.j) f) ≤ 1) → ∀ x ∈ U, RegAt x f := by
  first | exact @GlobalTheory.TrueGeo.RegCrit.regAt_of_integral_values | exact GlobalTheory.TrueGeo.RegCrit.regAt_of_integral_values | (intros; apply GlobalTheory.TrueGeo.RegCrit.regAt_of_integral_values <;> assumption)
