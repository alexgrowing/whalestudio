import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EssFiniteTypeOfFiniteDimensionalSubfieldClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringInValuationSubring

open Polynomial

namespace GlobalTheory

theorem exists_normal_finiteType_subring_le_valuationSubring :
    ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (V : ValuationSubring κ) (T : Finset κ),
    (∀ a : ℂ, algebraMap ℂ κ a ∈ V) → (∀ x ∈ T, x ∈ V) →
    (∀ f : κ, ∃ a ∈ Algebra.adjoin ℂ (T : Set κ), ∃ b ∈ Algebra.adjoin ℂ (T : Set κ), b ≠ 0 ∧ f * b = a) →
    ∃ (R : Subring κ) (hcR : ∀ a : ℂ, algebraMap ℂ κ a ∈ R),
      ((algebraMap ℂ κ).codRestrict R hcR).FiniteType ∧ (∀ x ∈ T, x ∈ R) ∧ R ≤ V.toSubring ∧
      IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R κ := by
  intro κ _ _ V T hc hT hgen
  classical
  haveI : CharZero κ := charZero_of_injective_algebraMap (algebraMap ℂ κ).injective
  let A : Subalgebra ℂ κ := Algebra.adjoin ℂ (T : Set κ)
  haveI : Algebra.FiniteType ℂ A := .adjoin_of_finite T.finite_toSet
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hAV : ∀ y ∈ A, y ∈ V := fun y hy => by
    let E' : Subalgebra ℂ κ := { V.toSubring with algebraMap_mem' := fun a => hc a }
    have : A ≤ E' := Algebra.adjoin_le fun x hx => hT x hx
    exact this hy
  haveI : Algebra.IsAlgebraic A κ := ⟨fun f => by
    obtain ⟨a, ha, b, hb, hb0, he⟩ := hgen f
    have hf : f = a / b := by rw [eq_div_iff hb0, he]
    have ha' : IsAlgebraic A a := isAlgebraic_algebraMap (⟨a, ha⟩ : A)
    have hb' : IsAlgebraic A b := isAlgebraic_algebraMap (⟨b, hb⟩ : A)
    rw [hf, div_eq_mul_inv]
    exact ha'.mul hb'.inv⟩
  have htop : Subfield.closure (Set.range (algebraMap ℂ κ) ∪ (T : Set κ)) = ⊤ := by
    refine eq_top_iff.mpr fun f _ => ?_
    have hle : A.toSubring ≤ (Subfield.closure (Set.range (algebraMap ℂ κ) ∪ (T : Set κ))).toSubring := by
      rw [show A.toSubring = Subring.closure (Set.range (algebraMap ℂ κ) ∪ (T : Set κ)) from
        Algebra.adjoin_eq_ring_closure _]
      exact Subring.closure_le.mpr Subfield.subset_closure
    obtain ⟨a, ha, b, hb, hb0, he⟩ := hgen f
    have hf : f = a / b := by rw [eq_div_iff hb0, he]
    rw [hf]
    exact Subfield.div_mem _ (hle ha) (hle hb)
  haveI : Algebra.EssFiniteType ℂ κ := by
    refine essFiniteType_of_finiteDimensional_subfield_closure T.finite_toSet ?_
    rw [htop]
    exact finiteDimensional_top_subfield κ
  haveI : Algebra.EssFiniteType A κ := .of_comp ℂ A κ
  haveI : Module.Finite A (integralClosure A κ) := finite_integralClosure_of_essFiniteType_field ℂ A κ
  let S := integralClosure A κ
  haveI : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  haveI : IsFractionRing S κ := integralClosure.isFractionRing_of_algebraic fun x hx => Subtype.ext hx
  haveI : IsIntegrallyClosed S := (isIntegrallyClosed_iff κ).mpr fun {x} hx =>
    ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩
  have hcR : ∀ a : ℂ, algebraMap ℂ κ a ∈ S.toSubring := fun a =>
    S.algebraMap_mem (⟨algebraMap ℂ κ a, A.algebraMap_mem a⟩ : A)
  refine ⟨S.toSubring, hcR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ S)
  · intro x hx
    exact S.algebraMap_mem (⟨x, Algebra.subset_adjoin hx⟩ : A)
  · intro x hx
    obtain ⟨q, hqm, hq⟩ := (hx : IsIntegral A x)
    let ι : A →+* V :=
      { toFun := fun a => ⟨a, hAV a a.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hE : IsIntegral V x := by
      refine ⟨q.map ι, hqm.map ι, ?_⟩
      rw [eval₂_map]
      exact hq
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hE
    exact y.2
  · exact (inferInstance : IsNoetherianRing S)
  · exact (inferInstance : IsIntegrallyClosed S)
  · exact (inferInstance : IsFractionRing S κ)

end GlobalTheory
