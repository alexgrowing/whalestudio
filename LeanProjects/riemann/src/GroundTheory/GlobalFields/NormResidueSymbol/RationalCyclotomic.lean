import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.Rational
import GroundTheory.GlobalFields.CyclotomicCharacters.ProfinitePadic

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace RationalSymbol

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

instance isGalois_maxCyclotomic : IsGalois ℚ maxCyclotomic := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  have h : @IsGalois ℚ _ maxCyclotomic _ (IntermediateField.algebra' maxCyclotomic) := by
    rw [← InfiniteGalois.normal_iff_isGalois, ← ker_character]
    infer_instance
  convert h
  exact Subsingleton.elim _ _

abbrev cycRestrict : Gal(ℚ̄/ℚ) →* Gal(maxCyclotomic/ℚ) :=
  AlgEquiv.restrictNormalHom maxCyclotomic

theorem cycRestrict_surjective : Function.Surjective cycRestrict := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  exact AlgEquiv.restrictNormalHom_surjective ℚ̄

theorem coe_cycRestrict_apply (σ : Gal(ℚ̄/ℚ)) (x : maxCyclotomic) :
    ((cycRestrict σ x : maxCyclotomic) : ℚ̄) = σ x :=
  AlgEquiv.restrictNormal_commutes σ maxCyclotomic x

theorem ker_cycRestrict : cycRestrict.ker = character.ker := by
  rw [ker_character]
  ext σ
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := coe_cycRestrict_apply σ ⟨x, hx⟩
    rw [h, AlgEquiv.one_apply] at this
    exact this.symm
  · intro h
    ext x
    rw [coe_cycRestrict_apply, AlgEquiv.one_apply]
    exact h x x.2

def cycCharacter : Gal(maxCyclotomic/ℚ) ≃* ℤ̂ˣ :=
  (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ker_cycRestrict).trans
      (QuotientGroup.quotientKerEquivOfSurjective character character_surjective))

theorem cycCharacter_cycRestrict (σ : Gal(ℚ̄/ℚ)) : cycCharacter (cycRestrict σ) = character σ := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm
      (cycRestrict σ) = (σ : Gal(ℚ̄/ℚ) ⧸ cycRestrict.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [cycCharacter, MulEquiv.trans_apply, MulEquiv.trans_apply, h]
  rfl

theorem cycCharacter_spec (τ : Gal(maxCyclotomic/ℚ)) (n : ℕ+) {ζ : maxCyclotomic}
    (hζ : ζ ^ (n : ℕ) = 1) :
    τ ζ = ζ ^ (ProfiniteInteger.proj n (cycCharacter τ : ℤ̂)).val := by
  obtain ⟨σ, rfl⟩ := cycRestrict_surjective τ
  apply Subtype.ext
  rw [cycCharacter_cycRestrict, SubmonoidClass.coe_pow]
  rw [coe_cycRestrict_apply]
  exact character_spec σ n (by rw [← SubmonoidClass.coe_pow, hζ, OneMemClass.coe_one])

def unitPart : IdeleClassGroup ℚ →* ℤ̂ˣ :=
  (Units.map padicEquiv.symm.toRingHom.toMonoidHom).comp
    ((MonoidHom.snd _ _).comp RationalIdeles.ideleClassGroupEquiv.toMulEquiv.toMonoidHom)

theorem unitPart_surjective : Function.Surjective unitPart := by
  intro w
  obtain ⟨x, hx⟩ := RationalIdeles.ideleClassGroupEquiv.surjective
    (1, Units.map padicEquiv.toRingHom.toMonoidHom w)
  refine ⟨x, Units.ext ?_⟩
  simp only [unitPart, MonoidHom.comp_apply, MonoidHom.coe_snd, Units.coe_map]
  change padicEquiv.symm ((RationalIdeles.ideleClassGroupEquiv x).2 : _) = _
  rw [hx]
  simp [ofPadics_toPadics]

theorem toPadicInt_unitPart (x : IdeleClassGroup ℚ) (q : Nat.Primes) :
    toPadicInt q (unitPart x : ℤ̂) =
      ((RationalIdeles.ideleClassGroupEquiv x).2 : Π p : Nat.Primes, ℤ_[p]) q := by
  change toPadics (padicEquiv.symm _) q = _
  rw [← padicEquiv_apply, RingEquiv.apply_symm_apply]
  rfl

def reciprocityMap : IdeleClassGroup ℚ →* Gal(maxCyclotomic/ℚ) :=
  cycCharacter.symm.toMonoidHom.comp unitPart⁻¹

theorem cycCharacter_reciprocityMap (x : IdeleClassGroup ℚ) :
    cycCharacter (reciprocityMap x) = (unitPart x)⁻¹ := by
  simp [reciprocityMap]

theorem reciprocityMap_surjective : Function.Surjective reciprocityMap := by
  intro τ
  obtain ⟨x, hx⟩ := unitPart_surjective (cycCharacter τ)⁻¹
  refine ⟨x, cycCharacter.injective ?_⟩
  rw [cycCharacter_reciprocityMap, hx, inv_inv]

theorem reciprocityMap_eq_one_iff (x : IdeleClassGroup ℚ) :
    reciprocityMap x = 1 ↔ (RationalIdeles.ideleClassGroupEquiv x).2 = 1 := by
  rw [← cycCharacter.injective.eq_iff, map_one, cycCharacter_reciprocityMap, inv_eq_one]
  have h : unitPart x =
      Units.map padicEquiv.symm.toRingHom.toMonoidHom (RationalIdeles.ideleClassGroupEquiv x).2 :=
    rfl
  rw [h, ← map_one (Units.map padicEquiv.symm.toRingHom.toMonoidHom)]
  exact (Units.map_injective (f := padicEquiv.symm.toRingHom.toMonoidHom)
    padicEquiv.symm.injective).eq_iff

end RationalSymbol

end

end GroundTheory.Global
