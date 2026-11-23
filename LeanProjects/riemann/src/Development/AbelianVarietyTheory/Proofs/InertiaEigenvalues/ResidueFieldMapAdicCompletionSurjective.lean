import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

open IsLocalRing

namespace GlobalTheory

theorem residueField_map_adicCompletion_surjective (W : Type*) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] :
    Function.Surjective (ResidueField.map (algebraMap W (AdicCompletion (maximalIdeal W) W))) := by
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal W) 1 x)
  refine ⟨residue W w, ?_⟩
  rw [ResidueField.map_residue, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
    mem_nonunits_iff]
  intro hu
  have h1 := hu.map (AdicCompletion.evalₐ (maximalIdeal W) 1)
  rw [map_sub, AlgHom.commutes, ← hw, Ideal.Quotient.algebraMap_eq, sub_self] at h1
  haveI : Nontrivial (W ⧸ maximalIdeal W ^ 1) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [pow_one]; exact (maximalIdeal.isMaximal W).ne_top)
  exact not_isUnit_zero h1

theorem finite_residueField_of_dominating (D : Type*) [CommRing D] [IsDomain D] [IsLocalRing D]
    [IsNoetherianRing D] [Ring.DimensionLEOne D] (hD : ¬ IsField D) [Finite (ResidueField D)]
    (V : ValuationSubring (FractionRing D))
    (h1 : ∀ r, algebraMap D (FractionRing D) r ∈ V)
    [IsLocalHom ((algebraMap D (FractionRing D)).codRestrict V h1)] :
    Finite (ResidueField V) := by
  set f := (algebraMap D (FractionRing D)).codRestrict V h1 with hf
  letI : Algebra D V := f.toAlgebra
  haveI : IsLocalHom (algebraMap D V) := ‹IsLocalHom f›
  haveI : FaithfulSMul D V := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    fun a b hab => IsFractionRing.injective D (FractionRing D) (congrArg Subtype.val hab)
  have hB : ∀ x : V, ∃ c : D, c ≠ 0 ∧ ∃ b : D, algebraMap D V c * x = algebraMap D V b := by
    intro x
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj (nonZeroDivisors D) (x : FractionRing D)
    refine ⟨c, nonZeroDivisors.coe_ne_zero c, b, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_mul] at hbc ⊢
    change algebraMap D (FractionRing D) c * x = algebraMap D (FractionRing D) b
    rw [mul_comm]; exact hbc
  have hm : maximalIdeal D ≠ ⊥ := fun h => hD (isField_iff_maximalIdeal_eq.mpr h)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  haveI := finite_quotient_span_of_birational hB ha0
  have hle : Ideal.span {algebraMap D V a} ≤ maximalIdeal V := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact map_nonunit (algebraMap D V) a ha
  have hsurj : Function.Surjective (Ideal.Quotient.factorₐ D hle).toLinearMap := by
    intro y
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ v, rfl⟩
  haveI : Module.Finite D (ResidueField V) := Module.Finite.of_surjective _ hsurj
  haveI : Module.Finite (ResidueField D) (ResidueField V) :=
    Module.Finite.of_restrictScalars_finite D _ _
  exact Module.finite_of_finite (ResidueField D)

theorem exists_complete_dvr_finite_residueField : ∀ (D : Type) [CommRing D] [IsDomain D] [IsLocalRing D], IsNoetherianRing D → ringKrullDim D = 1 → Finite (ResidueField D) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (maximalIdeal V) V) (g : D →+* V), Function.Injective g ∧ IsLocalHom g ∧ Finite (ResidueField V) := by
  intro D _ _ _ hN hdim hF
  have hD : ¬ IsField D := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hdim; exact zero_ne_one hdim
  haveI : Ring.KrullDimLE 1 D := Ring.krullDimLE_iff.mpr (by simp [hdim])
  haveI : Ring.DimensionLEOne D :=
    ⟨fun hp hpr => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp this _ hp hpr⟩
  obtain ⟨V, hV, h⟩ :=
    exists_discreteValuationSubring_dominating D (FractionRing D) (FractionRing D) hD
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  have hfin : Finite (ResidueField V) := finite_residueField_of_dominating D hD V h1
  obtain ⟨hi, hl⟩ := injective_and_isLocalHom_adicCompletion_comp
      ((algebraMap D (FractionRing D)).codRestrict V h1)
      fun a b hab => IsFractionRing.injective D (FractionRing D) (congrArg Subtype.val hab)
  exact ⟨AdicCompletion (maximalIdeal V) V, inferInstance, inferInstance, inferInstance,
    inferInstance, _, hi, hl,
    Finite.of_surjective _ (residueField_map_adicCompletion_surjective V)⟩

end GlobalTheory
