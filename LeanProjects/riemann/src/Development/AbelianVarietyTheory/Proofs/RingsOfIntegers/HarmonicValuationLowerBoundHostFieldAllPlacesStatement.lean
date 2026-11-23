import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValuationLowerBound_hostField_all_places : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n DFw : ℕ), Formalism.L2.Pj.DF Dw w ≤ DFw → ChBound C e (∑ p ∈ D.host.condN.primeFactors, (vV T.V (p : T.Fr) : ℝ) / e * D.host.vdH p * (DFw : ℝ) / 2) w n := by
  first | exact @GlobalTheory.PlaceInt.HostChart.chBound_host | exact GlobalTheory.PlaceInt.HostChart.chBound_host | (intros; apply GlobalTheory.PlaceInt.HostChart.chBound_host <;> assumption)
