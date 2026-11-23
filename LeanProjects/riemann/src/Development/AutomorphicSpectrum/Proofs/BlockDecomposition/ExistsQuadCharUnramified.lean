import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.UnramQuad

theorem exists_quadChar_unramified : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∃ η : Fˣ →* ℂˣ, (∀ a, ((η a : ℂˣ) : ℂ) = Ad3.K.GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧ Ad3.K.GL2LocalData.nsg E (-1 : F) = 1 := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hfin _ hord
  haveI : Fact (Module.finrank F E = 2) := ⟨hfin⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  have hf : (GroundTheory.LocalField.residueDegree F E : ℤ) = 2 := by
    have h := GroundTheory.LocalField.ord_norm (K := F) (L := E) (algebraMap F E (unifUnit F : F))
    rw [hord, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.norm_algebraMap_eq_sq,
      GroundTheory.LocalField.ord_pow (Units.ne_zero _), GroundTheory.LocalField.ord_unifUnit] at h
    simpa using h.symm
  have heven : ∀ a ∈ (normUnits F E).range, Even (GroundTheory.LocalField.ord (a : F)) := by
    rintro _ ⟨x, rfl⟩
    rw [coe_normUnits, GroundTheory.LocalField.ord_norm (K := F) (L := E), hf]
    exact even_two_mul _
  have hind := GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.index_range_normUnits_eq_two F E
  have hπ : unifUnit F ∉ (normUnits F E).range := fun h => by
    have := heven _ h
    rw [GroundTheory.LocalField.ord_unifUnit] at this
    exact absurd this (by decide)
  have hmem : ∀ a : Fˣ, a ∈ (normUnits F E).range ↔ Even (GroundTheory.LocalField.ord (a : F)) := by
    refine fun a => ⟨heven a, fun ha => ?_⟩
    by_contra hn
    have h1 : a * unifUnit F ∈ (normUnits F E).range :=
      (Subgroup.mul_mem_iff_of_index_two hind).2 (iff_of_false hn hπ)
    have h2 := heven _ h1
    rw [Units.val_mul, GroundTheory.LocalField.ord_mul (Units.ne_zero _) (Units.ne_zero _),
      GroundTheory.LocalField.ord_unifUnit] at h2
    exact (Int.even_add_one.1 h2) ha
  have hex : ∀ a : Fˣ, (∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)) ↔
      a ∈ (normUnits F E).range := by
    refine fun a => ⟨fun ⟨t, ht⟩ => ⟨t, Units.ext ((coe_normUnits t).trans ht)⟩, ?_⟩
    rintro ⟨t, rfl⟩
    exact ⟨t, (coe_normUnits t).symm⟩
  have hnsg : ∀ a : Fˣ, a ∈ (normUnits F E).range → Ad3.K.GL2LocalData.nsg E (a : F) = 1 := by
    intro a ha
    unfold Ad3.K.GL2LocalData.nsg
    rw [if_pos ((hex a).2 ha)]
  have hnsg' : ∀ a : Fˣ, a ∉ (normUnits F E).range → Ad3.K.GL2LocalData.nsg E (a : F) = -1 := by
    intro a ha
    unfold Ad3.K.GL2LocalData.nsg
    rw [if_neg (fun h => ha ((hex a).1 h))]
  refine ⟨GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar F E, fun a => ?_, ?_, ?_, ?_⟩
  · by_cases ha : a ∈ (normUnits F E).range
    · rw [GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ha, hnsg a ha, Units.val_one]
    · rw [GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_notMem ha, hnsg' a ha]
      simp
  · refine isUnramifiedChar_iff.2 fun u hu => ?_
    exact GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ((hmem u).2 (by rw [hu]; exact Even.zero))
  · ext t
    rw [MonoidHom.mul_apply, ← sq, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_sq]
    simp
  · have h0 : GroundTheory.LocalField.ord (-1 : F) = 0 := by
      have h := GroundTheory.LocalField.ord_mul (K := F) (x := -1) (y := -1) (by simp) (by simp)
      rw [neg_mul_neg, one_mul, GroundTheory.LocalField.ord_one] at h
      omega
    have := hnsg (-1) ((hmem (-1)).2 (by rw [Units.val_neg, Units.val_one, h0]; exact Even.zero))
    simpa using this

end GlobalTheory.CompanionTheory.SphTheta.UnramQuad
