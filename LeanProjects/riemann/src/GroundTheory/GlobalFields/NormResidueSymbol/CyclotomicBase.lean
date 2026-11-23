import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.Functorial
import GroundTheory.GlobalFields.NormResidueSymbol.Rational
import GroundTheory.GlobalFields.NormResidueSymbol.Surjective

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField

noncomputable section

namespace CyclotomicSymbol

section Roots

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem ideleSymbol_diagonal_apply_of_pow_eq_one (a : Kˣ) {n : ℕ} (hn : n ≠ 0) {ζ : L}
    (hζ : ζ ^ n = 1) : ideleSymbol K L (diagonal K a) ζ = ζ := by
  have hk : orderOf ζ ≠ 0 := (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨n, Nat.pos_of_ne_zero hn, hζ⟩)).ne'
  have : NeZero (orderOf ζ) := ⟨hk⟩
  have hprim : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
  set L₀ : IntermediateField ℚ L := ℚ⟮ζ⟯ with hL₀
  have : IsCyclotomicExtension {orderOf ζ} ℚ L₀ :=
    hprim.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsGalois ℚ L₀ := IsCyclotomicExtension.isGalois {orderOf ζ} ℚ L₀
  have : IsMulCommutative (L₀ ≃ₐ[ℚ] L₀) := IsCyclotomicExtension.isMulCommutative {orderOf ζ} ℚ L₀
  have h := restrictNormal_restrictScalars_ideleSymbol (K := ℚ) (L := L₀) (L' := L) (diagonal K a)
  rw [ideleNorm_diagonal, RationalSymbol.ideleSymbol_diagonal_eq_one L₀ {orderOf ζ}] at h
  have h' := congrArg (fun σ : L₀ ≃ₐ[ℚ] L₀ ↦ ((σ ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ : L₀) : L)) h
  simp only [AlgEquiv.one_apply] at h'
  exact (AlgEquiv.restrictNormal_commutes ((ideleSymbol K L (diagonal K a)).restrictScalars ℚ) L₀
    ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩).symm.trans h'

theorem ideleSymbol_diagonal_eq_one (S : Set ℕ) [IsCyclotomicExtension S K L] (a : Kˣ) :
    ideleSymbol K L (diagonal K a) = 1 :=
  IsCyclotomicExtension.algEquiv_eq_of_apply_eq S K L fun m hm hm0 ↦ by
    obtain ⟨r, hr⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L hm hm0
    exact ⟨r, hr, ideleSymbol_diagonal_apply_of_pow_eq_one a hm0 hr.pow_eq_one⟩

theorem ideleSymbol_diagonal_eq_one_of_isCyclotomicExtension_singleton (m : ℕ)
    [IsCyclotomicExtension {m} K L] (a : Kˣ) : ideleSymbol K L (diagonal K a) = 1 :=
  ideleSymbol_diagonal_eq_one {m} a

end Roots

section Sub

variable {K : Type*} [Field K] [NumberField K] (L M : Type*) [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M] [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (M ≃ₐ[K] M)]

theorem ideleSymbol_diagonal_eq_one_of_le (S : Set ℕ) [IsCyclotomicExtension S K M] (a : Kˣ) :
    ideleSymbol K L (diagonal K a) = 1 := by
  rw [← restrictNormal_ideleSymbol L M, ideleSymbol_diagonal_eq_one S a]
  exact map_one (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)

theorem range_diagonal_le_ker_ideleSymbol (S : Set ℕ) [IsCyclotomicExtension S K M] :
    (diagonal K).range ≤ (ideleSymbol K L).ker := by
  rintro _ ⟨a, rfl⟩
  exact ideleSymbol_diagonal_eq_one_of_le L M S a

end Sub

section ClassSymbol

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

def ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    IdeleClassGroup K →* (L ≃ₐ[K] L) :=
  QuotientGroup.lift _ (ideleSymbol K L) h

variable {L}

@[simp]
theorem ideleClassSymbol_mk (h : (diagonal K).range ≤ (ideleSymbol K L).ker) (x : IdeleGroup K) :
    ideleClassSymbol L h (IdeleClassGroup.mk K x) = ideleSymbol K L x :=
  rfl

theorem continuous_ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    Continuous (ideleClassSymbol L h) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_ideleSymbol L)

end ClassSymbol

universe u

theorem ideleClassSymbol_surjective {K L : Type u} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    Function.Surjective (ideleClassSymbol L h) := fun σ ↦
  let ⟨x, hx⟩ := ideleSymbol_surjective (K := K) (L := L) σ
  ⟨IdeleClassGroup.mk K x, hx⟩

end CyclotomicSymbol

end

end GroundTheory.Global
