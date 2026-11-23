import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonicalGaugeDifferenceBiadditiveJet
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalGauge_difference_biadditive_jet : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d), JRel m B B' φ φi ε → ∀ (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h h' lam : PS k 2 d), B.IsCanonGauge k h → B'.IsCanonGauge k h' → MvPowerSeries.constantCoeff lam = 0 → FB.expS k lam = FB.toK k ε → Biadd m B' k (h' - ev (n := 2) ![comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 0), comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 1)] h - lam) := by
  first | exact @GlobalTheory.ChartCmp.GaugeDiff.biadd_gauge_diff | exact GlobalTheory.ChartCmp.GaugeDiff.biadd_gauge_diff | (intros; apply GlobalTheory.ChartCmp.GaugeDiff.biadd_gauge_diff <;> assumption)
