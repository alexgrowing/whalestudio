import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtIntegralClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_finExt_fractionRing_of_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [Algebra (FractionRing R) E], FiniteDimensional (FractionRing R) E → IsGalois (FractionRing R) E → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (t : E →+* FractionRing R'), FinExt ρ ∧ ∀ r : R, t (algebraMap (FractionRing R) E (algebraMap R (FractionRing R) r)) = algebraMap R' (FractionRing R') (ρ r) := by
  intro R _ _ _ hR E _ _ hfd hgal
  obtain ⟨hloc, hfe⟩ := finExt_integralClosure (E := E) hR
  letI : Algebra R E := (baseMap R E).toAlgebra
  haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : CharZero R := hR.2
  set R₂ := integralClosure R E
  haveI : IsFractionRing R₂ E := integralClosure.isFractionRing_of_finite_extension (FractionRing R) E
  let t : E ≃ₐ[R₂] FractionRing R₂ := IsLocalization.algEquiv (nonZeroDivisors R₂) E (FractionRing R₂)
  refine ⟨R₂, inferInstance, inferInstance, hloc, algebraMap R R₂, t.toRingEquiv.toRingHom, hfe, ?_⟩
  intro r
  have h1 : algebraMap (FractionRing R) E (algebraMap R (FractionRing R) r) = algebraMap R₂ E (algebraMap R R₂ r) := rfl
  rw [h1]
  change t (algebraMap R₂ E _) = _
  rw [AlgEquiv.commutes]

end GlobalTheory.GalClosure
