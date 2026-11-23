import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothAdjoinInverse
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_adjoin_inverse : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 → Algebra.Smooth ℚ A → Algebra.Smooth ℚ (Mdl.invAdj A g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj <;> assumption)
