import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange

namespace GroundTheory.Global

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing NumberField.LiesOver

noncomputable section

namespace AdeleBaseChange

open SemiLocal

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

theorem completionMap_completionMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (u : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal]
    [u.asIdeal.LiesOver v.asIdeal] (a : v.adicCompletion K) :
    completionMap w u (completionMap v w a) = completionMap v u a := by
  have h := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    ((continuous_completionMap w u).comp (continuous_completionMap v w))
    (continuous_completionMap v u) (funext fun k ↦ ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply]
    rw [completionMap_algebraMap, completionMap_algebraMap,
      IsScalarTower.algebraMap_apply K L (w.adicCompletion L), completionMap_algebraMap,
      IsScalarTower.algebraMap_apply L M (u.adicCompletion M),
      IsScalarTower.algebraMap_apply K M (u.adicCompletion M), ← IsScalarTower.algebraMap_apply K L M]

omit [NumberField K] [NumberField L] [NumberField M] in

theorem below_below (u : HeightOneSpectrum (𝓞 M)) : below K (below L u) = below K u :=
  HeightOneSpectrum.ext (Ideal.under_under (A := 𝓞 K) (B := 𝓞 L) u.asIdeal)

theorem finiteAdeleMap_finiteAdeleMap (x : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleMap L M (finiteAdeleMap K L x) = finiteAdeleMap K M x := by
  refine FiniteAdeleRing.ext (K := M) fun u ↦ ?_
  have hb := below_below (K := K) (L := L) u
  have : u.asIdeal.LiesOver (below K (below L u)).asIdeal := by rw [hb]; infer_instance
  rw [finiteAdeleMap_apply, finiteAdeleMap_apply, finiteAdeleMap_apply,
    completionMap_completionMap (below K (below L u)) (below L u) u]
  exact completionMap_congr hb u x

omit [NumberField K] [NumberField L] [NumberField M] in

theorem algebraMap_completion_algebraMap (v : InfinitePlace K) (w : InfinitePlace L)
    (u : InfinitePlace M) [w.LiesOver v] [u.LiesOver w] [u.LiesOver v] (a : v.Completion) :
    algebraMap w.Completion u.Completion (algebraMap v.Completion w.Completion a) =
      algebraMap v.Completion u.Completion a := by
  have h := (InfinitePlace.Completion.denseRange_coe v).equalizer
    ((continuous_algebraMap w.Completion u.Completion).comp
      (continuous_algebraMap v.Completion w.Completion))
    (continuous_algebraMap v.Completion u.Completion) (funext fun y ↦ ?_)
  · exact congrFun h a
  · change algebraMap w.Completion u.Completion
        (algebraMap v.Completion w.Completion (algebraMap K v.Completion y.ofAbs)) =
      algebraMap v.Completion u.Completion (algebraMap K v.Completion y.ofAbs)
    rw [← IsScalarTower.algebraMap_apply K v.Completion w.Completion,
      ← IsScalarTower.algebraMap_apply K v.Completion u.Completion,
      IsScalarTower.algebraMap_apply K L w.Completion,
      ← IsScalarTower.algebraMap_apply L w.Completion u.Completion,
      IsScalarTower.algebraMap_apply L M u.Completion,
      IsScalarTower.algebraMap_apply K M u.Completion, ← IsScalarTower.algebraMap_apply K L M]

omit [NumberField K] [NumberField L] [NumberField M] [Algebra L M] [IsScalarTower K L M] in
theorem algebraMap_completion_congr {v v' : InfinitePlace K} (h : v = v') (u : InfinitePlace M)
    [u.LiesOver v] [u.LiesOver v'] (x : InfiniteAdeleRing K) :
    algebraMap v.Completion u.Completion (x v) = algebraMap v'.Completion u.Completion (x v') := by
  subst h
  rfl

omit [NumberField K] [NumberField L] [NumberField M] in

theorem infiniteAdeleRingMap_infiniteAdeleRingMap (x : InfiniteAdeleRing K) :
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := L) (L := M)
        (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := K) (L := L) x) =
      GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := K) (L := M) x := by
  funext u
  have hv : (u.comap (algebraMap L M)).comap (algebraMap K L) = u.comap (algebraMap K M) := by
    rw [IsScalarTower.algebraMap_eq K L M]
    rfl
  have : u.LiesOver ((u.comap (algebraMap L M)).comap (algebraMap K L)) := by
    rw [hv]; infer_instance
  rw [GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply,
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply,
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply,
    algebraMap_completion_algebraMap _ (u.comap (algebraMap L M)) u]
  exact algebraMap_completion_congr hv u x

theorem adeleMap_adeleMap (x : 𝔸[K]) : adeleMap L M (adeleMap K L x) = adeleMap K M x :=
  Prod.ext (infiniteAdeleRingMap_infiniteAdeleRingMap x.1) (finiteAdeleMap_finiteAdeleMap x.2)

scoped instance isScalarTower_adeleRing : IsScalarTower 𝔸[K] 𝔸[L] 𝔸[M] :=
  .of_algebraMap_eq fun x ↦ (adeleMap_adeleMap x).symm

theorem norm_adeleRing_norm (y : 𝔸[M]) :
    Algebra.norm 𝔸[K] (Algebra.norm 𝔸[L] y) = Algebra.norm 𝔸[K] y :=
  Algebra.norm_norm

end AdeleBaseChange

open AdeleBaseChange

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

theorem ideleEmbedding_ideleEmbedding (x : IdeleGroup K) :
    ideleEmbedding L M (ideleEmbedding K L x) = ideleEmbedding K M x :=
  Units.ext (adeleMap_adeleMap (x : 𝔸[K]))

theorem ideleNorm_ideleNorm (x : IdeleGroup M) :
    ideleNorm K L (ideleNorm L M x) = ideleNorm K M x :=
  Units.ext (norm_adeleRing_norm (K := K) (L := L) (x : 𝔸[M]))

theorem ideleClassMap_ideleClassMap (c : IdeleClassGroup K) :
    ideleClassMap L M (ideleClassMap K L c) = ideleClassMap K M c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [ideleClassMap_mk, ideleClassMap_mk, ideleClassMap_mk, ideleEmbedding_ideleEmbedding]

theorem ideleClassNorm_ideleClassNorm (c : IdeleClassGroup M) :
    ideleClassNorm K L (ideleClassNorm L M c) = ideleClassNorm K M c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective M c
  rw [ideleClassNorm_mk, ideleClassNorm_mk, ideleClassNorm_mk, ideleNorm_ideleNorm]

end

end GroundTheory.Global
