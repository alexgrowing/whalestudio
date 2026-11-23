import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegDataIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_integralClosure_isCN_finite_local : ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀], IsCN V₀ → ∀ (L : Type) [Field L] [Algebra (FractionRing V₀) L] [FiniteDimensional (FractionRing V₀) L], ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V₀ →+* V₁) (σ : L →+* FractionRing V₁), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ x : V₀, σ (algebraMap (FractionRing V₀) L (algebraMap V₀ (FractionRing V₀) x)) = algebraMap V₁ (FractionRing V₁) (ρ x) := by
  intro V₀ _ _ _ hV L _ _ _
  obtain ⟨hN, hIC, hC, hCZ⟩ := hV
  haveI := hN
  haveI := hIC
  haveI := hC
  haveI := hCZ
  let K₀ := FractionRing V₀
  letI : Algebra V₀ L := ((algebraMap K₀ L).comp (algebraMap V₀ K₀)).toAlgebra
  haveI : IsScalarTower V₀ K₀ L := .of_algebraMap_eq fun _ => rfl
  haveI : CharZero K₀ := IsFractionRing.charZero_of_isFractionRing V₀
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K₀ L).injective
  haveI : Algebra.IsSeparable K₀ L := inferInstance
  let V₁ := integralClosure V₀ L
  haveI : Module.Finite V₀ V₁ := IsIntegralClosure.finite V₀ K₀ L V₁
  haveI hN₁ : IsNoetherianRing V₁ := IsIntegralClosure.isNoetherianRing V₀ K₀ L V₁
  haveI : IsFractionRing V₁ L := IsIntegralClosure.isFractionRing_of_finite_extension V₀ K₀ L V₁
  haveI : IsIntegrallyClosed V₁ := integralClosure.isIntegrallyClosedOfFiniteExtension K₀
  haveI : HenselianLocalRing V₀ := GlobalTheory.henselianLocalRing_of_isAdicComplete V₀
  haveI : IsLocalRing V₁ := GlobalTheory.TameKummer.isLocalRing_of_finite V₀ V₁
  have hinj : Function.Injective (algebraMap V₀ V₁) := by
    intro a b h
    have h' := congrArg (algebraMap V₁ L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply V₀ K₀ L, IsScalarTower.algebraMap_apply V₀ K₀ L b] at h'
    exact IsFractionRing.injective V₀ K₀ ((algebraMap K₀ L).injective h')
  haveI : CharZero V₁ := charZero_of_injective_algebraMap hinj
  haveI : IsLocalHom (algebraMap V₀ V₁) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : (maximalIdeal V₁).comap (algebraMap V₀ V₁) = maximalIdeal V₀ :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
    have hmem : a ∈ (maximalIdeal V₁).comap (algebraMap V₀ V₁) := by
      rw [hm]; exact hna
    exact hmem ha
  have hcompl : IsAdicComplete (maximalIdeal V₁) V₁ :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V₀ V₁
  let e : L ≃ₐ[V₁] FractionRing V₁ := IsLocalization.algEquiv (nonZeroDivisors V₁) L (FractionRing V₁)
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, algebraMap V₀ V₁, e.toRingEquiv.toRingHom,
    ⟨hN₁, inferInstance, hcompl, inferInstance⟩, hinj, RingHom.finite_algebraMap.mpr inferInstance,
    inferInstance, fun x => ?_⟩
  have hx : algebraMap K₀ L (algebraMap V₀ K₀ x) = algebraMap V₁ L (algebraMap V₀ V₁ x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
  rw [hx, AlgEquiv.commutes]

end GlobalTheory.Poinc
