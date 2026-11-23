import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalCurveSmoothNearPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_curve_smooth_near_point : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsArithVar p 1 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ U : X.Opens, y ∈ ptsIn p σ U ∧ SmoothOfRelativeDimension 1 (U.ι ≫ p) := by
  first | exact @GlobalTheory.NormalGenSmooth.exists_opens_smooth_of_isNormalScheme | exact GlobalTheory.NormalGenSmooth.exists_opens_smooth_of_isNormalScheme | (intros; apply GlobalTheory.NormalGenSmooth.exists_opens_smooth_of_isNormalScheme <;> assumption)
