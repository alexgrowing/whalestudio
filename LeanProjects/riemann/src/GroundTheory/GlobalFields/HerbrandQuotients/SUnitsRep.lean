import Mathlib
import GroundTheory.GlobalFields.SUnits
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsPerm

namespace GroundTheory.Global

open NumberField IsDedekindDomain NumberField.Units
open scoped Pointwise

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

section Units

variable [NumberField L]

def unitsMap (g : L ≃ₐ[K] L) : (𝓞 L)ˣ →* (𝓞 L)ˣ :=
  Units.map (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) g : 𝓞 L →* 𝓞 L)

variable (K L) in

def unitsRep : Representation ℤ (L ≃ₐ[K] L) (Additive (𝓞 L)ˣ) where
  toFun g := (unitsMap g).toAdditive.toIntLinearMap
  map_one' := by
    refine LinearMap.ext fun u => ?_
    apply Additive.toMul.injective
    apply Units.ext
    apply RingOfIntegers.ext
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun u => ?_
    apply Additive.toMul.injective
    apply Units.ext
    apply RingOfIntegers.ext
    rfl

omit [NumberField L] in
theorem unitsRep_apply (g : L ≃ₐ[K] L) (u : Additive (𝓞 L)ˣ) :
    unitsRep K L g u = Additive.ofMul (unitsMap g u.toMul) :=
  rfl

end Units

section SUnits

variable [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L)))

theorem map_mem_unit (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) {x : Lˣ}
    (hx : x ∈ S.unit L) : Units.map (g : L →+* L).toMonoidHom x ∈ S.unit L := by
  intro w hw
  have hw' : g⁻¹ • w ∉ S := fun h => hw (by simpa using hS g _ h)
  have h1 := SemiLocal.valuation_smul g (g⁻¹ • w) (x : L)
  rw [smul_inv_smul] at h1
  change w.valuation L (g (x : L)) = 1
  rw [h1]
  exact hx _ hw'

def sUnitMap (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L) :
    S.unit L →* S.unit L :=
  ((Units.map (g : L →+* L).toMonoidHom).comp (S.unit L).subtype).codRestrict (S.unit L)
    fun x => map_mem_unit S hS g x.2

theorem coe_sUnitMap (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L)
    (x : S.unit L) : (((sUnitMap S hS g x : S.unit L) : Lˣ) : L) = g ((x : Lˣ) : L) :=
  rfl

def sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    Representation ℤ (L ≃ₐ[K] L) (Additive (S.unit L)) where
  toFun g := (sUnitMap S hS g).toAdditive.toIntLinearMap
  map_one' := by
    refine LinearMap.ext fun x => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rfl

theorem sUnitRep_apply (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L)
    (x : Additive (S.unit L)) :
    sUnitRep S hS g x = Additive.ofMul (sUnitMap S hS g x.toMul) :=
  rfl

theorem ofUnits_unitsRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L)
    (u : Additive (𝓞 L)ˣ) :
    (SUnit.ofUnits S).toAdditive (unitsRep K L g u) =
      sUnitRep S hS g ((SUnit.ofUnits S).toAdditive u) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rfl

theorem valuationVector_sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S)
    (g : L ≃ₐ[K] L) (x : Additive (S.unit L)) :
    letI := stableMulAction S hS
    SUnit.valuationVector S (sUnitRep S hS g x) =
      funPermRep ℤ (L ≃ₐ[K] L) S g (SUnit.valuationVector S x) := by
  let := stableMulAction S hS
  funext w
  rw [funPermRep_apply, ← ofMul_toMul x, sUnitRep_apply, toMul_ofMul,
    SUnit.valuationVector_apply, SUnit.valuationVector_apply]
  congr 1
  rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq,
    HeightOneSpectrum.valuationOfNeZero_eq, coe_sUnitMap]
  have h1 := SemiLocal.valuation_smul g (g⁻¹ • w.1) ((x.toMul : Lˣ) : L)
  rw [smul_inv_smul] at h1
  exact h1

end SUnits

end

end GroundTheory.Global
