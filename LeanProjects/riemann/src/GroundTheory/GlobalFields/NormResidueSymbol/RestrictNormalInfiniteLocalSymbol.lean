import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap

namespace GroundTheory.Global

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding
  SemiLocal AdeleBaseChange IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K] (L M : Type*) [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

section Finite

variable (v : HeightOneSpectrum (𝓞 K))

omit [NumberField K] [NumberField L] [NumberField M] in

theorem liesOver_below_of_placesOver (u : PlacesOver M v) :
    (below L u.1).asIdeal.LiesOver v.asIdeal :=
  (below_eq_iff _ v).1 (by rw [below_below, (below_eq_iff u.1 v).2 inferInstance])

def belowPlace (u : PlacesOver M v) : PlacesOver L v :=
  ⟨below L u.1, liesOver_below_of_placesOver L M v u⟩

omit [NumberField K] [NumberField L] [NumberField M] in
theorem belowPlace_val (u : PlacesOver M v) : (belowPlace L M v u).1 = below L u.1 :=
  rfl

omit [NumberField K] [NumberField L] [NumberField M] in

instance liesOver_belowPlace (u : PlacesOver M v) :
    u.1.asIdeal.LiesOver (belowPlace L M v u).1.asIdeal :=
  liesOver_below (K := L) u.1

def completionAlgHom (u : PlacesOver M v) :
    (belowPlace L M v u).1.adicCompletion L →ₐ[v.adicCompletion K] u.1.adicCompletion M :=
  { completionMap (belowPlace L M v u).1 u.1 with
    commutes' := fun a ↦ completionMap_completionMap v (belowPlace L M v u).1 u.1 a }

theorem completionAlgHom_algebraMap (u : PlacesOver M v) (l : L) :
    completionAlgHom L M v u (algebraMap L ((belowPlace L M v u).1.adicCompletion L) l) =
      algebraMap M (u.1.adicCompletion M) (algebraMap L M l) := by
  change completionMap _ u.1 _ = _
  rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply L M (u.1.adicCompletion M)]

variable [IsGalois K L] [IsGalois K M] [IsMulCommutative (L ≃ₐ[K] L)]
  [IsMulCommutative (M ≃ₐ[K] M)]

theorem restrictNormal_localSymbol (x : (v.adicCompletion K)ˣ) :
    (localSymbol M v x).restrictNormal L = localSymbol L v x := by
  obtain ⟨u⟩ := nonempty_placesOver M v
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := v.adicCompletion K) x
  have key : ∀ l : L,
      localSymbol M v x (algebraMap L M l) = algebraMap L M (localSymbol L v x l) := by
    intro l
    apply (algebraMap M (u.1.adicCompletion M)).injective
    apply (residueEmbedding (v.adicCompletion K) (u.1.adicCompletion M)).toRingHom.injective
    change residueEmbedding _ _ (algebraMap M _ (localSymbol M v x (algebraMap L M l))) =
      residueEmbedding _ _ (algebraMap M _ (algebraMap L M (localSymbol L v x l)))
    rw [algebraMap_localSymbol_apply M v u, residueEmbedding_normResidueSymbol hτ,
      ← completionAlgHom_algebraMap, ← completionAlgHom_algebraMap,
      algebraMap_localSymbol_apply L v (belowPlace L M v u)]
    exact (normResidueSymbol_spec
      ((residueEmbedding (v.adicCompletion K) (u.1.adicCompletion M)).comp
        (completionAlgHom L M v u)) hτ _).symm
  ext l
  apply (algebraMap L M).injective
  rw [AlgEquiv.restrictNormal_commutes, key]

end Finite

section Infinite

omit [NumberField K] [NumberField L] in

theorem isConj_conjAt_of_isReal [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) : IsConj w.embedding (conjAt K w) := by
  by_cases hw : w.IsReal
  · rw [conjAt_of_isReal hw]
    exact isConj_one_iff.2 (isReal_iff.1 hw)
  · exact isConj_conjAt (isRamified_iff.2 ⟨not_isReal_iff_isComplex.1 hw, hv⟩)

omit [NumberField K] [NumberField L] [NumberField M] in

theorem restrictNormal_conjAt [IsGalois K L] [IsGalois K M] (w : InfinitePlace M)
    (hv : (w.comap (algebraMap K M)).IsReal) :
    (conjAt K w).restrictNormal L = conjAt K (w.comap (algebraMap L M)) := by
  have h := isConj_conjAt_of_isReal M hv
  have hr : IsConj (w.embedding.comp (algebraMap L M)) ((conjAt K w).restrictNormal L) := by
    rw [isConj_iff_forall]
    intro l
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgEquiv.restrictNormal_commutes]
    exact h.eq _
  have hmk : mk (w.embedding.comp (algebraMap L M)) = mk (w.comap (algebraMap L M)).embedding := by
    rw [mk_embedding, ← comap_mk, mk_embedding]
  exact (conjOfEmbedding_eq ((isConj_iff_of_mk_eq hmk _).1 hr)).symm

variable [IsGalois K L] [IsGalois K M] [IsMulCommutative (L ≃ₐ[K] L)]
  [IsMulCommutative (M ≃ₐ[K] M)]

theorem restrictNormal_infiniteLocalSymbol (v : InfinitePlace K) (x : v.Completionˣ) :
    (infiniteLocalSymbol M v x).restrictNormal L = infiniteLocalSymbol L v x := by
  have h1 : (1 : M ≃ₐ[K] M).restrictNormal L = 1 :=
    map_one (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
  by_cases hv : v.IsReal
  · obtain ⟨w⟩ := IdeleNorm.nonempty_infinitePlacesOver M v
    have hwv : (w : InfinitePlace M).comap (algebraMap K M) = v :=
      (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq v _).1 w.2
    have hw' : ((w : InfinitePlace M).comap (algebraMap L M)).LiesOver v :=
      (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq v _).2 (by
        rw [← comap_comp, ← IsScalarTower.algebraMap_eq, hwv])
    rw [infiniteLocalSymbol_apply M v hv w, infiniteLocalSymbol_apply L v hv ⟨_, hw'⟩]
    split_ifs
    · exact restrictNormal_conjAt L M (w : InfinitePlace M) (by rw [hwv]; exact hv)
    · exact h1
  · rw [infiniteLocalSymbol_of_not_isReal M v hv, infiniteLocalSymbol_of_not_isReal L v hv]
    exact h1

end Infinite

variable [IsGalois K L] [IsGalois K M] [IsMulCommutative (L ≃ₐ[K] L)]
  [IsMulCommutative (M ≃ₐ[K] M)]

theorem restrictNormal_ideleSymbol (x : IdeleGroup K) :
    (ideleSymbol K M x).restrictNormal L = ideleSymbol K L x := by
  have h := eq_ideleSymbol L (ψ := (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).comp
      (ideleSymbol K M)) ((continuous_of_discreteTopology :
      Continuous (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)).comp (continuous_ideleSymbol M))
    (fun v a ↦ by
      rw [MonoidHom.comp_apply, ideleSymbol_finiteEmbedding]
      exact restrictNormal_localSymbol L M v a)
    (fun w a ↦ by
      rw [MonoidHom.comp_apply, ideleSymbol_infiniteEmbedding]
      exact restrictNormal_infiniteLocalSymbol L M w a)
  exact congrArg (fun f : IdeleGroup K →* (L ≃ₐ[K] L) ↦ f x) h

end

end GroundTheory.Global
