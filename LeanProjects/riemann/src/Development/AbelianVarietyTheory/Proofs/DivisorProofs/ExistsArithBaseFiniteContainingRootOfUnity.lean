import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_arithBase_rootOfUnity : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (Ω₂ : Type) [Field Ω₂] [Algebra Ω₁ Ω₂] (K : ℕ) (ζ : Ω₂ˣ), 0 < K → IsPrimitiveRoot ζ K → ∃ (o₂ : Type) (_ : CommRing o₂) (_ : Algebra o₂ Ω₂) (_ : ArithBase o₂ Ω₂) (κ : o₁ →+* o₂) (ze : o₂ˣ), κ.Finite ∧ (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) ∧ Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze = ζ := by
  intro o₁ Ω₁ _ _ _ hb Ω₂ _ _ K ζ hK hζ
  haveI := hb.ded
  haveI := hb.ft
  haveI := hb.char
  haveI hc₂ : CharZero Ω₂ := charZero_of_injective_algebraMap (algebraMap Ω₁ Ω₂).injective
  let f : o₁ →+* Ω₂ := (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)
  have hf : Function.Injective f := (algebraMap Ω₁ Ω₂).injective.comp hb.inj
  letI : Algebra o₁ Ω₂ := f.toAlgebra
  let Q := FractionRing o₁
  letI : Algebra Q Ω₂ := (IsFractionRing.lift (K := Q) hf).toAlgebra
  haveI : IsScalarTower o₁ Q Ω₂ := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsFractionRing.lift_algebraMap (K := Q) hf x).symm)
  haveI : CharZero Q := (algebraMap Q Ω₂).charZero
  have hpow : (ζ : Ω₂) ^ K = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  have hint : IsIntegral o₁ (ζ : Ω₂) := IsIntegral.of_pow hK (by rw [hpow]; exact isIntegral_one)
  let F : IntermediateField Q Ω₂ := IntermediateField.adjoin Q {(ζ : Ω₂)}
  haveI : FiniteDimensional Q F := IntermediateField.adjoin.finiteDimensional hint.tower_top
  haveI : IsDedekindDomain (integralClosure o₁ F) := integralClosure.isDedekindDomain o₁ Q F
  haveI hfin : Module.Finite o₁ (integralClosure o₁ F) := IsIntegralClosure.finite o₁ Q F _
  let g : integralClosure o₁ F →+* Ω₂ := (algebraMap F Ω₂).comp (algebraMap (integralClosure o₁ F) F)
  have hg : Function.Injective g := (algebraMap F Ω₂).injective.comp Subtype.val_injective
  let zF : F := ⟨ζ, IntermediateField.mem_adjoin_simple_self Q _⟩
  have hzF : zF ^ K = 1 := Subtype.ext (by simpa using hpow)
  let z : integralClosure o₁ F :=
    ⟨zF, IsIntegral.of_pow hK (by rw [hzF]; exact isIntegral_one)⟩
  have hz : z ^ K = 1 := Subtype.ext (by simpa using hzF)
  refine ⟨integralClosure o₁ F, inferInstance, g.toAlgebra,
    @ArithBase.mk _ _ _ _ g.toAlgebra inferInstance ?_ hc₂ hg,
    algebraMap o₁ (integralClosure o₁ F), Units.ofPowEqOne z K hz hK.ne', ?_, ?_, ?_⟩
  · exact Algebra.FiniteType.trans (S := o₁) inferInstance inferInstance
  · exact RingHom.finite_algebraMap.mpr hfin
  · ext x
    rfl
  · ext
    rfl

end GlobalTheory.Poinc
