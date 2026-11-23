import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameBorel_groupoid_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ y : FrPt Xo c S, FrBor 1 y y) ∧ (∀ (t t' : Ix Dw → Sˣ) (y y' y'' : FrPt Xo c S), FrBor t y y' → FrBor t' y' y'' → FrBor (t * t') y y'') ∧ (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t⁻¹ y' y) ∧ ∀ (t t' : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t' y y' → t = t' := by
  first | exact @GlobalTheory.Reg.BorelGroupoid.frBor_groupoid | exact GlobalTheory.Reg.BorelGroupoid.frBor_groupoid | (intros; apply GlobalTheory.Reg.BorelGroupoid.frBor_groupoid <;> assumption)
