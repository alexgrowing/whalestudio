import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveSingularPointsFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_singular_points_finite : ∀ (κ : Type) [Field κ] [CharZero κ] (C : Scheme.{0}) [Algebra κ Γ(C, ⊤)] [IsIntegral C], IsProjCurve κ C → {x : C | ¬ IsPrincipalIdealRing (C.presheaf.stalk x)}.Finite := by
  first | exact @GlobalTheory.CurvePID.finite_not_isPrincipalIdealRing | exact GlobalTheory.CurvePID.finite_not_isPrincipalIdealRing | (intros; apply GlobalTheory.CurvePID.finite_not_isPrincipalIdealRing <;> assumption)
