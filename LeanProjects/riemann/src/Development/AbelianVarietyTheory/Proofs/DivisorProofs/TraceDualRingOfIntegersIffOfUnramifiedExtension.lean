import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped nonZeroDivisors

namespace GlobalTheory.UnrTraceDual

theorem traceDual_ringOfIntegers_iff_of_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔ ∀ d ∈ differentIdeal ℤ (𝓞 F), IsIntegral ℤ (algebraMap F E (d : F) * e) := by
  intro F E _ _ _ _ _ hU e
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := inferInstance
  have hEq : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
      (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu, Ideal.top_mul]
  have hint : ∀ x : E, IsIntegral ℤ x ↔ x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    intro x
    rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]
  have h1 : (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔
      e ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
    constructor
    · intro h a ha
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 ha
      rw [Algebra.traceForm_apply, mul_comm]
      exact RingHom.mem_range.2 (IsIntegrallyClosed.isIntegral_iff.1 (h o))
    · intro h o
      have := h (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff (𝓞 E)⁰).2 ⟨o, rfl⟩)
      rw [Algebra.traceForm_apply, mul_comm] at this
      exact IsIntegrallyClosed.isIntegral_iff.2 (RingHom.mem_range.1 this)
  have h2 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  have hne : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  rw [h1, h2, FractionalIdeal.mem_inv_iff hne, hEq]
  let J : Ideal (𝓞 E) :=
    { carrier := {x | IsIntegral ℤ (algebraMap (𝓞 E) E x * e)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add, add_mul] at *
        exact ha.add hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero, zero_mul]
        exact isIntegral_zero
      smul_mem' := by
        intro c x hx
        have hx' : IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := hx
        have hc : IsIntegral ℤ (algebraMap (𝓞 E) E c) := RingOfIntegers.isIntegral_coe c
        show IsIntegral ℤ (algebraMap (𝓞 E) E (c * x) * e)
        rw [map_mul, mul_assoc]
        exact IsIntegral.mul hc hx' }
  have hJ : ∀ x : 𝓞 E, x ∈ J ↔ IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := fun _ => Iff.rfl
  have hL : (∀ y ∈ (((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) : Ideal (𝓞 E)) :
      FractionalIdeal (𝓞 E)⁰ E), e * y ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔
      (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) ≤ J := by
    constructor
    · intro h x hx
      rw [hJ, hint, mul_comm]
      exact h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hx)
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
      rw [mul_comm, ← hint]
      exact (hJ x).1 (h hx)
  rw [hL, Ideal.map_le_iff_le_comap]
  constructor
  · intro h d hd
    have := (hJ _).1 (h hd)
    rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
  · intro h d hd
    show algebraMap (𝓞 F) (𝓞 E) d ∈ J
    rw [hJ, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    exact h d hd

end GlobalTheory.UnrTraceDual
