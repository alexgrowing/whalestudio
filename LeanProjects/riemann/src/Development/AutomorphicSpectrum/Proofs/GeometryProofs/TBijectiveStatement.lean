import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TBijective
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_logPeriods_T : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (i : Fin a), Function.Bijective (L.T i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij.T_bijective | exact GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij.T_bijective | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij.T_bijective <;> assumption)
