import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsComponentInChartRegular
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_component_in_chart_regular : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (tie : CoordTie ℤ ξ (seg y)) (Q : Ideal (MRing J))
    (hQ : Q.IsPrime) (hle : mCoordIdeal y ≤ Q) (c : ∀ k, J k)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ Q),
    ∃ P : Cpt ξ, InChart ξ (seg y) c P ∧ ∀ a ∈ regAt ξ P, RegAt y Q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime <;> assumption)
