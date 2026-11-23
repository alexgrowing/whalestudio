import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.IsScalarTowerFiniteSubfieldAlgebraicClosure
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.SemiLocal FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
  {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]

instance isScalarTower_finiteSubfield_of_fact : IsScalarTower K.1 F.1 E.1 :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable (F E) in

def completionEmbeddingBelow (u : PlacesOver F.1 v)
    [(placeOfEmbedding ι E).1.asIdeal.LiesOver u.1.asIdeal] :
    u.1.adicCompletion F.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1) :=
  { (completionEmbedding ι E).toRingHom.comp (completionMap u.1 (placeOfEmbedding ι E).1) with
    commutes' a := by
      change completionEmbedding ι E (completionMap u.1 (placeOfEmbedding ι E).1
        (completionMap v u.1 a)) = _
      rw [AdeleBaseChange.completionMap_completionMap v u.1 (placeOfEmbedding ι E).1 a]
      exact (completionEmbedding ι E).commutes a }

theorem completionEmbeddingBelow_apply (u : PlacesOver F.1 v)
    [(placeOfEmbedding ι E).1.asIdeal.LiesOver u.1.asIdeal] (a : u.1.adicCompletion F.1) :
    completionEmbeddingBelow ι F E u a =
      completionEmbedding ι E (completionMap u.1 (placeOfEmbedding ι E).1 a) :=
  rfl

theorem completionEmbeddingBelow_algebraMap (u : PlacesOver F.1 v)
    [(placeOfEmbedding ι E).1.asIdeal.LiesOver u.1.asIdeal] (x : F.1) :
    completionEmbeddingBelow ι F E u (algebraMap F.1 _ x) = ι x := by
  rw [completionEmbeddingBelow_apply, completionMap_algebraMap,
    IsScalarTower.algebraMap_apply F.1 E.1 ((placeOfEmbedding ι E).1.adicCompletion E.1),
    completionEmbedding_algebraMap]
  rfl

theorem below_placeOfEmbedding_liesOver :
    (AdeleBaseChange.below F.1 (placeOfEmbedding ι E).1).asIdeal.LiesOver v.asIdeal := by
  rw [← AdeleBaseChange.below_eq_iff, AdeleBaseChange.below_below,
    AdeleBaseChange.below_eq_iff]
  exact (placeOfEmbedding ι E).2

theorem below_placeOfEmbedding :
    (⟨AdeleBaseChange.below F.1 (placeOfEmbedding ι E).1, below_placeOfEmbedding_liesOver ι⟩ :
      PlacesOver F.1 v) = placeOfEmbedding ι F :=
  eq_placeOfEmbedding ι F (completionEmbeddingBelow ι F E _)
    (completionEmbeddingBelow_algebraMap ι _)

instance liesOver_placeOfEmbedding :
    (placeOfEmbedding ι E).1.asIdeal.LiesOver (placeOfEmbedding ι F).1.asIdeal := by
  rw [← below_placeOfEmbedding ι (F := F) (E := E)]
  exact AdeleBaseChange.liesOver_below _

theorem completionEmbedding_completionMap (a : (placeOfEmbedding ι F).1.adicCompletion F.1) :
    completionEmbedding ι E (completionMap (placeOfEmbedding ι F).1 (placeOfEmbedding ι E).1 a) =
      completionEmbedding ι F a := by
  have : completionEmbeddingBelow ι F E (placeOfEmbedding ι F) = completionEmbedding ι F :=
    algHom_ext_adicCompletion F fun x ↦ by
      rw [completionEmbeddingBelow_algebraMap, completionEmbedding_algebraMap]
  exact DFunLike.congr_fun this a

end

end GroundTheory.ProfCoh
