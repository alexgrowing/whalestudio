import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicUniformizationDiffUnique
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_uniformization_diff_unique : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), SmoothOfRelativeDimension g A.hom → ConnectedSpace A.left → ∀ (v : epsR ℂ ⟶ A), ¬ IsTangent v → ∀ (w w' : Fin g → ℂ), u.IsDiff w v → u.IsDiff w' v → w = w' := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.DualFibre.eq_of_isDiff_of_not_isTangent | exact GlobalTheory.CompanionTheory.Ggeo.DualFibre.eq_of_isDiff_of_not_isTangent | (intros; apply GlobalTheory.CompanionTheory.Ggeo.DualFibre.eq_of_isDiff_of_not_isTangent <;> assumption)
