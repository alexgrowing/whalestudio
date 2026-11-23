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

noncomputable section

namespace GlobalTheory.NormBlPrincipal

theorem idlAlong_comap_principal : ∀ {S Z : Scheme.{0}} (π : S ⟶ Z) (J : Z.IdealSheafData), IsNormBl π J →
    ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S), ∃ g₀ : R, idlAlong (J.comap π) ξ = Ideal.span {g₀} := by
  intro S Z π J h R _ _ ξ
  obtain ⟨-, S₀, π₀, ν, -, hbl, hc, -⟩ := h
  obtain ⟨U, f, hx, -, hU⟩ := hbl.1 ((ξ ≫ ν) (closedPoint R))
  have hle : ⊤ ≤ (ξ ≫ ν) ⁻¹ᵁ U.1 := (Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ ν) hx).ge
  refine ⟨((ξ ≫ ν).appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom f, ?_⟩
  have e : idlAlong (J.comap π) ξ = idlAlong (J.comap π₀) (ξ ≫ ν) := by
    rw [GlobalTheory.PullAlong.idlAlong_comap_eq, GlobalTheory.PullAlong.idlAlong_comap_eq, ← hc, Category.assoc]
  rw [e, GlobalTheory.TraitOrder.idlAlong_eq_map _ _ U hle, hU, Ideal.map_span, Set.image_singleton]

end GlobalTheory.NormBlPrincipal
