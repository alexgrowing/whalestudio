import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyCx

open TensorProduct in

theorem exists_dominant_component :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (g : R →+* ℂ), ∃ (E : Type) (_ : CommRing E) (_ : IsDomain E) (_ : Algebra ℂ E) (ρ : R →+* E) (e : E →ₐ[ℂ] ℂ), Algebra.FiniteType ℂ E ∧ Function.Injective ρ ∧ e.toRingHom.comp ρ = g := by
  intro R _ _ _ g
  letI : Algebra R (ℂ ⊗[ℤ] R) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Flat R (ℂ ⊗[ℤ] R) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight ℤ R ℂ).symm.toLinearEquiv
  let e₀ : (ℂ ⊗[ℤ] R) →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) g.toIntAlgHom (fun _ _ => Commute.all _ _)
  have he : ∀ r : R, e₀ (algebraMap R (ℂ ⊗[ℤ] R) r) = g r := by
    intro r
    change e₀ (1 ⊗ₜ r) = g r
    simp [e₀]
  let Q : Ideal (ℂ ⊗[ℤ] R) := RingHom.ker e₀.toRingHom
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hqQ, hq, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal R)) (q := Q.under R) Q bot_le
  refine ⟨(ℂ ⊗[ℤ] R) ⧸ q, inferInstance, inferInstance, inferInstance,
    (Ideal.Quotient.mk q).comp (algebraMap R _),
    Ideal.Quotient.liftₐ q e₀ (fun a ha => hqQ ha), inferInstance, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro r hr
    have h1 : r ∈ q.under R :=
      Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    rw [← hlo.over] at h1
    exact h1
  · ext r
    exact he r

end GlobalTheory.KeyCx
