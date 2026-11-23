import Mathlib
import GroundTheory.GlobalFields.Artin.Brauer
import GroundTheory.GlobalFields.Artin.OneDimExistence
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField IntermediateField Filter Topology Set Complex

namespace GroundTheory.Global

open GroundTheory.LocalField

section Group

variable {G : Type*} [Group G] [Fintype G]

theorem charInner_character_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    charInner G ρ.character 1 = Module.finrank ℂ ρ.invariants := by
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let _ : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero hG
  rw [← (ρ.isProj_averageMap).trace, charInner_apply]
  simp [Representation.character, GroupAlgebra.average, map_sum, Nat.card_eq_fintype_card]

theorem charInner_indFun_char_one (H : Subgroup G) [Fintype H] (l : H →* ℂˣ) :
    charInner G (indFun H.subtype (fun k ↦ (l k : ℂ))) 1 = if l = 1 then 1 else 0 := by
  rw [charInner_indFun _ _ (fun _ _ ↦ rfl), charInner_apply]
  simp only [Function.comp_apply, Pi.one_apply, mul_one]
  split_ifs with h
  · subst h
    have hH : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    simp [Nat.card_eq_fintype_card] at hH ⊢
  · have hψ : (Units.coeHom ℂ).comp l ≠ 1 := by
      intro h1
      apply h
      ext k
      exact congrArg Units.val (Units.ext (DFunLike.congr_fun h1 k) : l k = 1) ▸ rfl
    have hs : ∑ k : H, ((l k : ℂˣ) : ℂ) = 0 := sum_hom_units_eq_zero _ hψ
    rw [hs, mul_zero]

theorem ne_one_of_charInner_sum_indFun_eq_zero {ι : Type*} [Fintype ι] {H : ι → Subgroup G}
    [∀ i, Fintype (H i)] (n : ι → ℕ) (l : ∀ i, H i →* ℂˣ)
    (h : charInner G (∑ i, n i • indFun (H i).subtype (fun k ↦ (l i k : ℂ))) 1 = 0) (i : ι)
    (hi : n i ≠ 0) : l i ≠ 1 := by
  classical
  have hsum : charInner G (∑ i, n i • indFun (H i).subtype (fun k ↦ (l i k : ℂ))) 1 =
      ((∑ i, n i * if l i = 1 then 1 else 0 : ℕ) : ℂ) := by
    rw [map_sum, LinearMap.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_nsmul, LinearMap.smul_apply, charInner_indFun_char_one, nsmul_eq_mul]
  rw [hsum, Nat.cast_eq_zero, Finset.sum_eq_zero_iff] at h
  intro hl
  have := h i (Finset.mem_univ i)
  rw [if_pos hl, mul_one] at this
  exact hi this

end Group

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem not_exists_cpow_of_isOfFinOrder (ψ : HeckeCharacter K) (hψ : IsOfFinOrder ψ) (hne : ψ ≠ 1) :
    ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (ψ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  rintro ⟨τ, hτ⟩
  apply hne
  obtain ⟨n, hn, hpow⟩ := ψ.exists_toIdele_pow_eq_one hψ
  let w : InfinitePlace K := Classical.arbitrary _
  have hs : ∀ t : {x : ℝ // 0 < x}, ψ.toIdele (moduleSection w t) = 1 := by
    intro t
    have ht : (⟨(t : ℝ) ^ (n⁻¹ : ℝ), Real.rpow_pos_of_pos t.2 _⟩ : {x : ℝ // 0 < x}) ^ n = t :=
      Subtype.ext (by simp [Real.rpow_inv_natCast_pow t.2.le hn.ne'])
    rw [← ht, map_pow, map_pow]
    exact hpow _
  have h0 : archExponent w ψ = 0 := archExponent_unique w ψ fun t ↦ by simp [hs t]
  have hτ0 : τ = 0 := (archExponent_eq_of_forall hτ w).symm.trans h0
  refine ContinuousMonoidHom.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  have hx := hτ x
  rw [hτ0] at hx
  simp only [ofReal_zero, zero_mul, cpow_zero] at hx
  rw [← toIdele_apply]
  exact Circle.ext (by simpa using hx)

end HeckeCharacter

section Hecke

universe u

theorem eq_one_of_heckeCharacterOfChar_eq_one {K L : Type u} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (χ : Gal(L/K) →* ℂˣ) (h : heckeCharacterOfChar χ = 1) :
    χ = 1 := by
  ext σ
  obtain ⟨c, hc⟩ := reciprocityMap_surjective (K := K) (L := ↥(charField χ))
    (AlgEquiv.restrictNormalHom (charField χ) σ)
  have h1 := heckeCharacterOfChar_apply χ c
  rw [h, hc, charBar_restrictNormalHom] at h1
  simpa using h1.symm

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem not_exists_cpow_heckeCharacterOfChar_fixedFieldChar (H : Subgroup Gal(L/K)) (l : H →* ℂˣ)
    (hl : l ≠ 1) :
    ¬ ∃ τ : ℝ, ∀ x : IdeleGroup (fixedField H),
      ((heckeCharacterOfChar (fixedFieldChar H l)).toIdele x : ℂ) =
        ((IdeleGroup.ideleModule (fixedField H) x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  refine HeckeCharacter.not_exists_cpow_of_isOfFinOrder _ (isOfFinOrder_heckeCharacterOfChar _)
    fun h ↦ hl ?_
  have h1 := eq_one_of_heckeCharacterOfChar_eq_one _ h
  ext k
  have := DFunLike.congr_fun h1 (Artin.fixedFieldMulEquiv H k)
  simpa [fixedFieldChar] using congrArg Units.val this

end Hecke

end GroundTheory.Global
