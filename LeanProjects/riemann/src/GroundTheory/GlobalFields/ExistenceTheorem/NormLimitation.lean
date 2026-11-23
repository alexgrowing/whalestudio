import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.General
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup AdeleBaseChange

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section MaxAbelian

variable (K M : Type*) [Field K] [Field M] [Algebra K M]

def maxAbelian : IntermediateField K M := fixedField (commutator Gal(M/K))

variable [FiniteDimensional K M] [IsGalois K M]

instance isGalois_maxAbelian : IsGalois K (maxAbelian K M) :=
  IsGalois.of_fixedField_normal_subgroup _

instance isMulCommutative_maxAbelian : IsMulCommutative Gal(maxAbelian K M/K) := by
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  let e : Gal(M/K) ⧸ commutator Gal(M/K) ≃* Gal(maxAbelian K M/K) :=
    IsGalois.normalAutEquivQuotient (commutator Gal(M/K))
  obtain ⟨a, rfl⟩ := e.surjective σ
  obtain ⟨b, rfl⟩ := e.surjective τ
  rw [← map_mul, ← map_mul]
  exact congrArg e (mul_comm (G := Abelianization Gal(M/K)) a b)

instance isAbelianGalois_maxAbelian : IsAbelianGalois K (maxAbelian K M) where

theorem finrank_maxAbelian :
    Module.finrank K (maxAbelian K M) = Nat.card (Abelianization Gal(M/K)) := by
  have h1 := Module.finrank_mul_finrank K (maxAbelian K M) M
  rw [maxAbelian, finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M,
    ← (commutator Gal(M/K)).card_mul_index] at h1
  have hpos : 0 < Nat.card (commutator Gal(M/K)) := Nat.card_pos
  rw [mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos h1

end MaxAbelian

namespace IdeleClassLimit

open FiniteSubfield GroundTheory.LocalField.Abstract

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

theorem ker_abstractSymbol_le :
    (abstractSymbol K L).ker ≤ (FiniteSubfield.ideleClassNorm hKL.out).range := by
  intro c hc
  rw [MonoidHom.mem_ker, abstractSymbol_apply] at hc
  have hinj : Function.Injective (Abelianization.map (quotientGaloisEquiv K L).toMonoidHom) :=
    fun a b hab ↦ (quotientGaloisEquiv K L).abelianizationCongr.injective hab
  rw [← map_one (Abelianization.map (quotientGaloisEquiv K L).toMonoidHom), hinj.eq_iff,
    ← map_one (reciprocityEquiv K L).symm, (reciprocityEquiv K L).symm.injective.eq_iff] at hc
  change (QuotientGroup.mk (fixedEquiv K c) : tateZero IdeleClassLimit
    (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) L.openSubgroup) = 1 at hc
  rw [QuotientGroup.eq_one_iff] at hc
  obtain ⟨b, hb⟩ := hc
  obtain ⟨d, rfl⟩ := (fixedEquiv L).surjective b
  refine ⟨d, (fixedEquiv K).injective ?_⟩
  rw [← norm_fixedEquiv hKL.out d]
  exact hb

theorem index_range_ideleClassNorm_dvd :
    (FiniteSubfield.ideleClassNorm hKL.out).range.index ∣
      Nat.card (Abelianization (L.1 ≃ₐ[K.1] L.1)) := by
  refine (Subgroup.index_dvd_of_le (ker_abstractSymbol_le K L)).trans ?_
  rw [Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card (abstractSymbol K L).range

end IdeleClassLimit

section Transport

theorem index_range_ideleClassNorm_dvd_card_abelianization {K M : Type*} [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] [IsGalois K M] :
    (ideleClassNorm K M).range.index ∣ Nat.card (Abelianization Gal(M/K)) := by
  let K' := baseField K M
  let M' := topField M
  let _ : Algebra K K'.1 := (rangeMap (baseEmbedding K M)).toAlgebra
  let _ : Algebra M M'.1 := (rangeMap (embedding M)).toAlgebra
  let _ : Algebra K M'.1 := ((rangeMap (embedding M)).comp (algebraMap K M)).toAlgebra
  have : IsScalarTower K K'.1 M'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K M M'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hK : Function.Bijective (algebraMap K K'.1) := rangeMap_bijective _
  have hM : Function.Bijective (algebraMap M M'.1) := rangeMap_bijective _
  have : IsGalois K M'.1 :=
    IsGalois.of_algEquiv (AlgEquiv.ofBijective (IsScalarTower.toAlgHom K M M'.1) hM)
  have : IsGalois K'.1 M'.1 := IsGalois.tower_top_of_isGalois K K'.1 M'.1
  have := FiniteSubfield.normal_subgroupOf_of_isGalois (F := K') (E := M')
  have h1 := IdeleClassLimit.index_range_ideleClassNorm_dvd K' M'
  have hrange : (ideleClassNorm K M).range =
      (ideleClassNorm K'.1 M'.1).range.map (ideleClassNorm K K'.1) := by
    ext c
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨ideleClassNorm K'.1 M'.1 (ideleClassMap M M'.1 d), ⟨_, rfl⟩, ?_⟩
      rw [ideleClassNorm_ideleClassNorm, ← ideleClassNorm_ideleClassNorm (L := M),
        ideleClassNorm_ideleClassMap, finrank_eq_one_of_bijective hM, pow_one]
    · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
      exact ⟨ideleClassNorm M M'.1 d, by
        rw [ideleClassNorm_ideleClassNorm, ideleClassNorm_ideleClassNorm]⟩
  have hsurj : Function.Surjective (ideleClassNorm K K'.1) := fun c ↦
    ⟨ideleClassMap K K'.1 c, by
      rw [ideleClassNorm_ideleClassMap, finrank_eq_one_of_bijective hK, pow_one]⟩
  have hcard : Nat.card (Abelianization Gal(M'.1/K'.1)) = Nat.card (Abelianization Gal(M/K)) := by
    let f : Gal(M'.1/K'.1) →* Gal(M/K) :=
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M'.1) M).comp (restrictScalarsHom K)
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro σ hσ
      exact restrictNormal_restrictScalars_eq_one (K := K) hM hσ
    have hc : Nat.card Gal(M'.1/K'.1) = Nat.card Gal(M/K) := by
      rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
      have e1 := Module.finrank_mul_finrank K K'.1 M'.1
      have e2 := Module.finrank_mul_finrank K M M'.1
      rw [finrank_eq_one_of_bijective hK, one_mul] at e1
      rw [finrank_eq_one_of_bijective hM, mul_one] at e2
      rw [e1, e2]
    have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hc.ge
    exact Nat.card_congr (MulEquiv.ofBijective f hbij).abelianizationCongr.toEquiv
  rw [hrange, ← hcard]
  exact (Subgroup.index_map_dvd _ hsurj).trans h1

universe u

variable {K M : Type u} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

theorem range_ideleClassNorm_maxAbelian :
    (ideleClassNorm K (maxAbelian K M)).range = (ideleClassNorm K M).range := by
  have hle : (ideleClassNorm K M).range ≤ (ideleClassNorm K (maxAbelian K M)).range := by
    rintro _ ⟨c, rfl⟩
    exact ⟨ideleClassNorm (maxAbelian K M) M c, ideleClassNorm_ideleClassNorm c⟩
  have hE : (ideleClassNorm K (maxAbelian K M)).range.index =
      Nat.card (Abelianization Gal(M/K)) := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative, finrank_maxAbelian]
  have hne : (ideleClassNorm K (maxAbelian K M)).range.index ≠ 0 := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative]
    exact Module.finrank_pos.ne'
  have heq : (ideleClassNorm K M).range.index = (ideleClassNorm K (maxAbelian K M)).range.index :=
    Nat.dvd_antisymm (hE ▸ index_range_ideleClassNorm_dvd_card_abelianization)
      (Subgroup.index_dvd_of_le hle)
  have hrel := Subgroup.relIndex_mul_index hle
  rw [heq] at hrel
  have h1 : (ideleClassNorm K M).range.relIndex (ideleClassNorm K (maxAbelian K M)).range = 1 := by
    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (hrel.trans (one_mul _).symm)
    exact this
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hle

theorem index_range_ideleClassNorm_eq_card_abelianization :
    (ideleClassNorm K M).range.index = Nat.card (Abelianization Gal(M/K)) := by
  rw [← range_ideleClassNorm_maxAbelian, index_range_ideleClassNorm_eq_finrank_of_isMulCommutative,
    finrank_maxAbelian]

omit [IsGalois K M] in

theorem exists_isAbelianGalois_range_ideleClassNorm_le (L : Type u) [Field L] [NumberField L]
    [Algebra K L] :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (_ : Algebra K E),
      IsAbelianGalois K E ∧ (ideleClassNorm K E).range ≤ (ideleClassNorm K L).range := by
  let Ω := AlgebraicClosure L
  have : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans K L Ω
  have : IsAlgClosure K Ω := ⟨AlgebraicClosure.isAlgClosed L, inferInstance⟩
  let N := normalClosure K L Ω
  have : IsGalois K N := ⟨⟩
  have : NumberField N := NumberField.of_module_finite K N
  refine ⟨maxAbelian K N, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [range_ideleClassNorm_maxAbelian]
  rintro _ ⟨c, rfl⟩
  exact ⟨ideleClassNorm L N c, ideleClassNorm_ideleClassNorm c⟩

end Transport

end

end GroundTheory.Global
