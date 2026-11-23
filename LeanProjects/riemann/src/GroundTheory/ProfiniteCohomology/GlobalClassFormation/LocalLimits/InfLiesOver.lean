import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfDefs
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.LiesOver
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField GroundTheory.Global FiniteSubfield NumberField.InfinitePlace.Completion

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
  {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]

theorem comap_liesOver (w' : v.placesOver E.1) :
    ((w' : NumberField.InfinitePlace E.1).comap (algebraMap F.1 E.1)).LiesOver v := by
  rw [GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq, ← NumberField.InfinitePlace.comap_comp,
    ← IsScalarTower.algebraMap_eq, ← GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq]
  exact w'.2

theorem completionMap_algebraMap_completion (u : NumberField.InfinitePlace F.1)
    (w' : NumberField.InfinitePlace E.1) [w'.LiesOver u] [u.LiesOver v] [w'.LiesOver v]
    (c : v.Completion) :
    NumberField.LiesOver.completionMap (v := u) (w := w') (algebraMap v.Completion u.Completion c) =
      algebraMap v.Completion w'.Completion c := by
  have h := (denseRange_coe v).equalizer
    ((NumberField.LiesOver.continuous_completionMap).comp
      (continuous_algebraMap v.Completion u.Completion))
    (continuous_algebraMap v.Completion w'.Completion) (funext fun a ↦ ?_)
  · exact congrFun h c
  · simp only [Function.comp_apply]
    change algebraMap u.Completion w'.Completion
      (algebraMap v.Completion _ (algebraMap K.1 v.Completion (WithAbs.ofAbs a))) =
      algebraMap v.Completion _ (algebraMap K.1 v.Completion (WithAbs.ofAbs a))
    rw [← IsScalarTower.algebraMap_apply K.1 v.Completion u.Completion,
      ← IsScalarTower.algebraMap_apply K.1 v.Completion w'.Completion,
      IsScalarTower.algebraMap_apply K.1 F.1, ← IsScalarTower.algebraMap_apply F.1,
      IsScalarTower.algebraMap_apply K.1 E.1 w'.Completion,
      IsScalarTower.algebraMap_apply F.1 E.1 w'.Completion]
    rfl

variable (F E) in

def infCompletionEmbeddingBelow (u : v.placesOver F.1)
    [(infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (u : NumberField.InfinitePlace F.1)] :
    (u : NumberField.InfinitePlace F.1).Completion →ₐ[v.Completion] AlgebraicClosure v.Completion :=
  { (infCompletionEmbedding ι E).toRingHom.comp (NumberField.LiesOver.completionMap
      (v := (u : NumberField.InfinitePlace F.1))
      (w := (infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1))) with
    commutes' c := by
      change infCompletionEmbedding ι E (NumberField.LiesOver.completionMap
        (algebraMap v.Completion _ c)) = _
      rw [completionMap_algebraMap_completion]
      exact (infCompletionEmbedding ι E).commutes c }

theorem infCompletionEmbeddingBelow_algebraMap (u : v.placesOver F.1)
    [(infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (u : NumberField.InfinitePlace F.1)] (x : F.1) :
    infCompletionEmbeddingBelow ι F E u (algebraMap F.1 _ x) = ι x := by
  change infCompletionEmbedding ι E (algebraMap u.1.Completion _ (algebraMap F.1 _ x)) = ι x
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F.1 E.1,
    infCompletionEmbedding_algebraMap]
  rfl

instance liesOver_infPlaceOfEmbedding :
    (infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1) := by
  have hu := comap_liesOver (F := F) (infPlaceOfEmbedding ι E)
  let u : v.placesOver F.1 := ⟨_, hu⟩
  have : (infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1).LiesOver
      (u : NumberField.InfinitePlace F.1) :=
    (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq _ _).2 rfl
  have h := eq_infPlaceOfEmbedding ι F (infCompletionEmbeddingBelow ι F E u)
    (infCompletionEmbeddingBelow_algebraMap ι u)
  rw [← h]
  exact this

theorem infCompletionEmbedding_completionMap
    (a : (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion) :
    infCompletionEmbedding ι E (NumberField.LiesOver.completionMap
      (v := (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1))
      (w := (infPlaceOfEmbedding ι E : NumberField.InfinitePlace E.1)) a) =
      infCompletionEmbedding ι F a := by
  have : infCompletionEmbeddingBelow ι F E (infPlaceOfEmbedding ι F) = infCompletionEmbedding ι F :=
    algHom_ext_infCompletion F fun x ↦ by
      rw [infCompletionEmbeddingBelow_algebraMap, infCompletionEmbedding_algebraMap]
  exact DFunLike.congr_fun this a

end

end GroundTheory.ProfCoh
