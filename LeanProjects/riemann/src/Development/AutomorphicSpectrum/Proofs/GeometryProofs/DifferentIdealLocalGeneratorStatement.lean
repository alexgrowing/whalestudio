import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentIdealLocalGenerator
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_ideal_local_generator : ∀ (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [CharZero Ω] (R : Subring Ω) [IsLocalRing R] (σ : 𝓞 F →+* Ω), (∀ a, σ a ∈ R) → ∃ d₀ ∈ differentIdeal ℤ (𝓞 F), σ d₀ ≠ 0 ∧ ∀ d ∈ differentIdeal ℤ (𝓞 F), σ d / σ d₀ ∈ R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.differentIdeal_principal_in_localSubring | exact GlobalTheory.CompanionTheory.Ar.differentIdeal_principal_in_localSubring | (intros; apply GlobalTheory.CompanionTheory.Ar.differentIdeal_principal_in_localSubring <;> assumption)
