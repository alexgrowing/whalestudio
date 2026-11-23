import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafAlongLocalSpecNormalisedBlowupPrincipa
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafAlongLocalSpec_normalisedBlowup_principal : ∀ {S Z : Scheme.{0}} (π : S ⟶ Z) (J : Z.IdealSheafData), IsNormBl π J → ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S), ∃ g₀ : R, idlAlong (J.comap π) ξ = Ideal.span {g₀} := by
  first | exact @GlobalTheory.NormBlPrincipal.idlAlong_comap_principal | exact GlobalTheory.NormBlPrincipal.idlAlong_comap_principal | (intros; apply GlobalTheory.NormBlPrincipal.idlAlong_comap_principal <;> assumption)
