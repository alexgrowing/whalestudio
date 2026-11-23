import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectivePointImageReduced
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_point_image_reduced : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (hx : x ≠ 0), IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.closure_reduced_dominant | exact GlobalTheory.CompanionTheory.Ar.SncRes.closure_reduced_dominant | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.closure_reduced_dominant <;> assumption)
