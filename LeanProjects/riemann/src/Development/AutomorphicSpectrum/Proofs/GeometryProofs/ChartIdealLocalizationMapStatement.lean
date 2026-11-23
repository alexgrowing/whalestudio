import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartIdealLocalizationMap
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCoverAndCone
import ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ideal_localization_map : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ (R : Type) [CommRing R] (θ : MvPolynomial (Σ k, J k) ℂ →+* R),
    (∀ g ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c, θ g = 0) →
    ∀ (F : MvPolynomial (Σ k, J k) ℚ), IsUnit (θ (map (algebraMap ℚ ℂ) F)) →
    ∀ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) F : Ω)⁻¹
        (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)) →
    ∃ ψ : S →+* R, ∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S),
      (s : Ω) = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G → ψ s = θ (map (algebraMap ℚ ℂ) G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart | exact GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart <;> assumption)
