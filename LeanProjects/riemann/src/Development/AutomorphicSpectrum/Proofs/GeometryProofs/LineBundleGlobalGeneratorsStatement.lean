import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleGlobalGenerators
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_global_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (Λ : Lat ξ Ω), CoordTie ℤ ξ x → Λ.IsVB 1 ⊤ → ∃ (n m : ℕ) (s : Fin (m + 1) → Ω), (∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∀ i, s i / x c ^ n ∈ Λ p) ∧ ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ i, Λ.IsGenAt p (s i / x c ^ n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.line_twist_generated | exact GlobalTheory.CompanionTheory.Ar.line_twist_generated | (intros; apply GlobalTheory.CompanionTheory.Ar.line_twist_generated <;> assumption)
