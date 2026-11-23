import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem integralClosure_galois_finite_invariants :
    ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L], letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra; Module.Finite A (integralClosure A L) ∧ Finite (integralClosure A L ≃ₐ[A] integralClosure A L) ∧ Function.Injective (algebraMap A (integralClosure A L)) ∧ ∀ b : integralClosure A L, (∀ σ : integralClosure A L ≃ₐ[A] integralClosure A L, σ b = b) → b ∈ Set.range (algebraMap A (integralClosure A L)) := by
  intro A K L _ _ _ _ _ _ _ _ _ _ _
  letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsSeparable K L := inferInstance
  refine ⟨IsIntegralClosure.finite A K L (integralClosure A L), ?_, ?_, ?_⟩
  · exact Finite.of_equiv _ (galRestrict A K L (integralClosure A L)).toEquiv
  · intro x y h
    have h' := congrArg (algebraMap (integralClosure A L) L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at h'
    exact IsFractionRing.injective A K ((algebraMap K L).injective h')
  · intro b hb
    haveI : IsFractionRing (integralClosure A L) L :=
      integralClosure.isFractionRing_of_finite_extension K L
    have := Algebra.isInvariant_of_isGalois' A K L (integralClosure A L)
    exact this.isInvariant b hb

end GlobalTheory.Poinc
