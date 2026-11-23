import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExplicitArithmeticHilbertSamuelBound
import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicit_arithmetic_hilbertSamuel_bound : Quoted → BertiniNF → HeightTie → SlopeBound → GeoBound := by
  first | exact @GlobalTheory.HSShortTop.geoBound_of_abstract | exact GlobalTheory.HSShortTop.geoBound_of_abstract | (intros; apply GlobalTheory.HSShortTop.geoBound_of_abstract <;> assumption)
