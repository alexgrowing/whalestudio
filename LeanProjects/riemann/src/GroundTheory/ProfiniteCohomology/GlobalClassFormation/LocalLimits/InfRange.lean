import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfLiesOver
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.ApplyCompletionEmbeddingOfLocalDecompHomEqOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField GroundTheory.Global FiniteSubfield

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

section Level

variable (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

theorem infLocalDecompHom_surjective : Function.Surjective (infLocalDecompHom ι F) := by
  intro τ
  let _ : Algebra (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
      (AlgebraicClosure v.Completion) := (infCompletionEmbedding ι F).toRingHom.toAlgebra
  have : IsScalarTower v.Completion (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
      (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ ((infCompletionEmbedding ι F).commutes a).symm
  let ψ := infiniteDecompositionToLocal v (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1) τ
  refine ⟨ψ.liftNormal (AlgebraicClosure v.Completion), Subtype.ext ?_⟩
  rw [coe_infLocalDecompHom, decompHom_eq_iff]
  intro x
  rw [infEmbedLevel_apply, infEmbedLevel_apply, ← infCompletionEmbedding_algebraMap,
    ← infCompletionEmbedding_algebraMap]
  change algebraMap _ (AlgebraicClosure v.Completion)
      (algebraMap F.1 (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion (τ.1 x)) =
    (ψ.liftNormal (AlgebraicClosure v.Completion)) (algebraMap _ _
      (algebraMap F.1 (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion x))
  rw [AlgEquiv.liftNormal_commutes, infiniteDecompositionToLocal_apply]
  exact congrArg (algebraMap _ (AlgebraicClosure v.Completion))
    (infiniteDecomposition_smul_coe τ (WithAbs.toAbs _ x)).symm

omit [F.1.fixingSubgroup.Normal] in

theorem isComplex_infPlaceOfEmbedding {r : F.1} (hr : r ^ 2 = -1) :
    (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).IsComplex := by
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hreal
  let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal
  have h : e (algebraMap F.1 _ r) ^ 2 = -1 := by
    rw [← map_pow, ← map_pow, hr, map_neg, map_one, map_neg, map_one]
  have := sq_nonneg (e (algebraMap F.1 _ r))
  rw [h] at this
  linarith

omit [F.1.fixingSubgroup.Normal] in

theorem isAlgClosed_infCompletion {r : F.1} (hr : r ^ 2 = -1) :
    IsAlgClosed (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion :=
  IsAlgClosed.of_ringEquiv ℂ _
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (isComplex_infPlaceOfEmbedding ι F hr)).symm

omit [F.1.fixingSubgroup.Normal] in

theorem infCompletionEmbedding_surjective {r : F.1} (hr : r ^ 2 = -1) :
    Function.Surjective (infCompletionEmbedding ι F) := by
  have := isAlgClosed_infCompletion ι F hr
  let _ : Algebra (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
      (AlgebraicClosure v.Completion) := (infCompletionEmbedding ι F).toRingHom.toAlgebra
  have : IsScalarTower v.Completion (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
      (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ ((infCompletionEmbedding ι F).commutes a).symm
  have : Algebra.IsIntegral (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion
      (AlgebraicClosure v.Completion) := Algebra.IsIntegral.tower_top v.Completion
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)
    (K := AlgebraicClosure v.Completion)).2

theorem infLocalDecompHom_injective (hF : Function.Surjective (infCompletionEmbedding ι F)) :
    Function.Injective (infLocalDecompHom ι F) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply AlgEquiv.ext
  intro α
  obtain ⟨y, rfl⟩ := hF α
  have h1 := infCompletionEmbedding_smul ι F σ y
  have h2 : infLocalDecompHom ι F σ • y = y := by
    rw [hσ]
    exact one_smul _ y
  rw [h2] at h1
  exact h1.symm

end Level

theorem exists_level_infCompletionEmbedding_surjective :
    ∃ p₀ : GLevel K, ∀ p : GLevel K, p₀ ≤ p → Function.Surjective (infCompletionEmbedding ι p.1) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℚ̄) two_pos
  obtain ⟨p₀, hr₀⟩ := exists_level_mem (K := K) r
  refine ⟨p₀, fun p hp ↦ ?_⟩
  have hrp : r ∈ p.1.1 := (show p₀.1.1 ≤ p.1.1 from hp) hr₀
  exact infCompletionEmbedding_surjective ι p.1 (r := ⟨r, hrp⟩) (Subtype.ext hr)

end

end GroundTheory.ProfCoh
