import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.HilbertClassFieldModels
import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import GroundTheory.GlobalFields.Artin.InflationTower
import GroundTheory.GlobalFields.Artin.OneDim
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField IsDedekindDomain Module IntermediateField WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Restrict

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {H L : IntermediateField K Ω}
  (h : H ≤ L)

def galRestrict [Normal K H] : (L ≃ₐ[K] L) →* (H ≃ₐ[K] H) :=
  letI : Algebra H L := (inclusion h).toAlgebra
  haveI : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  AlgEquiv.restrictNormalHom H

theorem galRestrict_apply [Normal K H] (σ : L ≃ₐ[K] L) (z : H) :
    ((galRestrict h σ z : H) : Ω) = (σ (inclusion h z) : Ω) := by
  letI : Algebra H L := (inclusion h).toAlgebra
  haveI : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact congrArg Subtype.val (AlgEquiv.restrictNormal_commutes σ H z)

theorem galRestrict_surjective [Normal K H] [Normal K L] :
    Function.Surjective (galRestrict h) := by
  letI : Algebra H L := (inclusion h).toAlgebra
  haveI : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := H) (E := L)

theorem mem_fixingSubgroup_restrict_iff [Normal K H] (σ : L ≃ₐ[K] L) :
    σ ∈ (restrict h).fixingSubgroup ↔ galRestrict h σ = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hσ
    ext z
    rw [galRestrict_apply, hσ _ ((mem_restrict h _).2 z.2)]
    rfl
  · intro hσ a ha
    have e := galRestrict_apply h σ ⟨a.1, (mem_restrict h a).1 ha⟩
    rw [hσ] at e
    exact Subtype.ext e.symm

end Restrict

section Frobenius

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem exists_isArithFrobAt_galRestrict {H L : IntermediateField K ℂ} [NumberField H]
    [NumberField L] [IsGalois K H] [IsGalois K L] (h : H ≤ L) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] (σ : L ≃ₐ[K] L)
    (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal) :
    ∃ w' : HeightOneSpectrum (𝓞 H), w'.asIdeal.LiesOver v.asIdeal ∧
      IsArithFrobAt (𝓞 K) (galRestrict h σ) w'.asIdeal := by
  letI : Algebra H L := (inclusion h).toAlgebra
  haveI : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨HeightOneSpectrum.under (𝓞 H) w, ?_, ?_⟩
  · have : w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 H) w).asIdeal :=
      ⟨by rw [HeightOneSpectrum.under_asIdeal]⟩
    exact Ideal.LiesOver.tower_bot w.asIdeal _ v.asIdeal
  · rw [HeightOneSpectrum.under_asIdeal]
    exact IsArithFrobAt.restrictNormalHom (F := H) hσ

theorem galRestrict_eq_of_isArithFrobAt {L : IntermediateField K ℂ} [NumberField L] [IsGalois K L]
    (hHL : hilbertClassField K ℂ ≤ L) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] (σ : L ≃ₐ[K] L)
    (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal) :
    galRestrict hHL σ = hilbertClassFieldArtinEquiv K ℂ (primeClass v) := by
  obtain ⟨w', hw', h1⟩ := exists_isArithFrobAt_galRestrict hHL v w σ hσ
  rw [hilbertClassFieldArtinEquiv_mk0 K ℂ v w']
  have hram : w'.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    (isUnramifiedIn_iff_ramificationIdx K (hilbertClassField K ℂ) v).1
      ((isUnramifiedEverywhere_hilbertClassField K ℂ).1 v) w' hw'
  have hI : w'.asIdeal.inertia (hilbertClassField K ℂ ≃ₐ[K] hilbertClassField K ℂ) = ⊥ := by
    rw [← Subgroup.card_eq_one, natCard_inertia v w', hram]
  exact IsArithFrobAt.eq_of_inertia_eq_bot hI h1 (IsArithFrobAt.arithFrobAt _ _ _)

end Frobenius

section Main

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

include hK in

theorem galClassOf_eq_artin (L : IntermediateField K ℂ) [FiniteDimensional K L] [IsGalois K L]
    (hHL : hilbertClassField K ℂ ≤ L) (hL : ∀ x : ELL K, ELL.j x ∈ L)
    (E : ELL K → WeierstrassCurve L) [∀ x, (E x).IsElliptic]
    (hE : ∀ x, ∃ h : Nonempty (isogEnd ((E x).baseChange ℂ) ≃+* 𝓞 K),
      (⟨(E x).baseChange ℂ, h⟩ : CMCurve K).toEll = x)
    (hiso : ∀ x y, Nonempty (Isogeny (E x) (E y))) (τ : L ≃ₐ[K] L) :
    galClassOf hK L hL τ = (hilbertClassFieldArtinEquiv K ℂ).symm (galRestrict hHL τ) := by
  classical
  haveI : NumberField L := NumberField.of_module_finite K L
  set β : (L ≃ₐ[K] L) →* ClassGroup (𝓞 K) :=
    (hilbertClassFieldArtinEquiv K ℂ).symm.toMonoidHom.comp (galRestrict hHL)
  change galClassOf hK L hL τ = β τ
  obtain ⟨S, hS, hfrob⟩ := frobenius_at_primes_of_degree_one hK hL E hE hiso
  have key : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∈ degreeOnePrimes ℚ K →
      ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
        galClassOf hK L hL (arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal) =
          β (arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal) := by
    intro v hvS hv1 w hw
    have hσ := IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal
    rw [((hfrob v hvS hv1 w).2.1 _ hσ).1]
    change _ = (hilbertClassFieldArtinEquiv K ℂ).symm (galRestrict hHL _)
    rw [galRestrict_eq_of_isArithFrobAt hHL v w _ hσ, MulEquiv.symm_apply_apply]
  set C : Set (L ≃ₐ[K] L) := {ρ | IsConj τ ρ}
  have hC : ∀ σ ∈ C, ∀ ρ : L ≃ₐ[K] L, ρ * σ * ρ⁻¹ ∈ C := fun σ hσ ρ ↦
    IsConj.trans hσ (isConj_iff.2 ⟨ρ, rfl⟩)
  have hdens := hasDirichletDensity_setOf_arithFrobAt_mem C hC
  rw [← hasDirichletDensity_inter_degreeOnePrimes_iff ℚ] at hdens
  haveI : Nonempty C := ⟨⟨τ, IsConj.refl τ⟩⟩
  have hpos : (0 : ℝ) < Nat.card C / Nat.card (L ≃ₐ[K] L) :=
    div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  obtain ⟨v, ⟨hvA, hv1⟩, hvS⟩ :
      (({v : HeightOneSpectrum (𝓞 K) | ∀ w : HeightOneSpectrum (𝓞 L),
        w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧
          arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal ∈ C} ∩ degreeOnePrimes ℚ K) \ S).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hne
    have h0 := hasDirichletDensity_zero_of_finite (hS.subset hne)
    have := hdens.dirichletDensity_eq.symm.trans h0.dirichletDensity_eq
    linarith
  obtain ⟨⟨w, hw⟩⟩ := nonempty_placesOver L v
  obtain ⟨c, hc⟩ := isConj_iff.1 (hvA w hw).2
  have e := key v hvS hv1 w hw
  rw [← hc] at e
  have conj : ∀ f : (L ≃ₐ[K] L) →* ClassGroup (𝓞 K), f (c * τ * c⁻¹) = f τ := fun f ↦ by
    rw [map_mul, map_mul, map_inv, mul_comm (f c), mul_inv_cancel_right]
  rwa [conj, conj] at e

end Main

end

end Elliptic
end GroundTheory.Global
