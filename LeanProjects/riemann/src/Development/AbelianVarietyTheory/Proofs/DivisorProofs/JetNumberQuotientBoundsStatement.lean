import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberQuotientBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_number_quotient_bounds : Size → Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → JetNum (Fm.D x ι) (DF (dat p i) (aOf p i u1)) (1 / 2500) ∧ 2 * (Fm.D x ι).R.r ≤ nCol (dat p i) ∧ (lenT p i PP : ℝ) * (Real.log ((Fm.D x ι).host.g 0) + Real.log ((Fm.D x ι).host.g 1)) ≤ C * unitE p := by
  first | exact @GlobalTheory.RefSum.NumPt.numbers_at_point | exact GlobalTheory.RefSum.NumPt.numbers_at_point | (intros; apply GlobalTheory.RefSum.NumPt.numbers_at_point <;> assumption)
