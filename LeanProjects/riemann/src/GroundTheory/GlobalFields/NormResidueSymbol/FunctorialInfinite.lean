import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol

namespace GroundTheory.Global

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
  NumberField.ComplexEmbedding IdeleGroup
open scoped NumberField.LiesOver

noncomputable section

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

theorem ideleNorm_infiniteEmbedding (v' : InfinitePlace K') (a : v'.Completionˣ) :
    ideleNorm K K' (infiniteEmbedding v' a) =
      infiniteEmbedding (v'.comap (algebraMap K K'))
        (LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a) := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun w ↦ ?_) (FiniteAdeleRing.ext (K := K) fun v ↦ ?_)
  · rw [ideleNorm_fst]
    simp only [coe_infiniteEmbedding]
    by_cases hw : w = v'.comap (algebraMap K K')
    · subst hw
      rw [Finset.prod_eq_single (⟨v', (inferInstance : v'.LiesOver (v'.comap (algebraMap K K')))⟩ :
          (v'.comap (algebraMap K K')).placesOver K'),
        infiniteAdeleSingle_apply, infiniteAdeleSingle_apply, Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_same, LocalField.coe_normUnits]
      · intro u _ hu
        rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne (fun h ↦ hu (Subtype.ext h)),
          map_one]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hw]
      refine Finset.prod_eq_one fun u _ ↦ ?_
      have hu : (u : InfinitePlace K') ≠ v' := by
        rintro h
        apply hw
        rw [← h]
        exact ((GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq w _).1 u.2).symm
      rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hu, map_one]
  · rw [ideleNorm_snd]
    exact Finset.prod_eq_one fun _ _ ↦ map_one _

variable {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra K L]
  [Algebra K L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']

omit [NumberField K] [NumberField K'] [NumberField L] [NumberField L'] in

theorem restrictNormal_restrictScalars_conjAt [IsGalois K L] [IsGalois K' L']
    (u' : InfinitePlace L') (hv : (u'.comap (algebraMap K' L')).IsReal) :
    ((conjAt K' u').restrictScalars K).restrictNormal L = conjAt K (u'.comap (algebraMap L L')) := by
  have h := isConj_conjAt_of_isReal L' hv
  have hr : IsConj (u'.embedding.comp (algebraMap L L'))
      (((conjAt K' u').restrictScalars K).restrictNormal L) := by
    rw [isConj_iff_forall]
    intro l
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgEquiv.restrictNormal_commutes,
      AlgEquiv.restrictScalars_apply]
    exact h.eq _
  have hmk : mk (u'.embedding.comp (algebraMap L L')) =
      mk (u'.comap (algebraMap L L')).embedding := by
    rw [mk_embedding, ← comap_mk, mk_embedding]
  exact (conjOfEmbedding_eq ((isConj_iff_of_mk_eq hmk _).1 hr)).symm

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]

omit [NumberField K] [NumberField K'] [NumberField L] [NumberField L'] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L'] [IsMulCommutative (L' ≃ₐ[K'] L')] in

theorem restrictNormal_restrictScalars_one [Normal K L] :
    ((1 : L' ≃ₐ[K'] L').restrictScalars K).restrictNormal L = 1 := by
  ext l
  apply (algebraMap L L').injective
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply, AlgEquiv.one_apply,
    AlgEquiv.one_apply]

omit [NumberField K] [NumberField K'] in

theorem extensionEmbeddingOfIsReal_normUnits (v' : InfinitePlace K') (hv' : v'.IsReal)
    (a : v'.Completionˣ) :
    extensionEmbeddingOfIsReal (hv'.comap (algebraMap K K'))
        (LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a : _) =
      extensionEmbeddingOfIsReal hv' a := by
  have hv := hv'.comap (algebraMap K K')
  have hfin : Module.finrank (v'.comap (algebraMap K K')).Completion v'.Completion = 1 :=
    (GroundTheory.Global.InfinitePlace.finrank_completion_eq_one_iff v').2
      fun h ↦ not_isComplex_iff_isReal.2 hv' h.2
  obtain ⟨c, hc⟩ := ((Algebra.finrank_eq_one_iff_bijective_algebraMap).1 hfin).2
    (a : v'.Completion)
  have e1 : (extensionEmbeddingOfIsReal hv'
      (algebraMap (v'.comap (algebraMap K K')).Completion v'.Completion c) : ℂ) =
        extensionEmbeddingOfIsReal hv c := by
    rw [extensionEmbeddingOfIsReal_apply]
    exact GroundTheory.Global.InfinitePlace.extensionEmbedding_algebraMap hv c
  rw [LocalField.coe_normUnits, ← hc, Algebra.norm_algebraMap, hfin, pow_one]
  exact (Complex.ofReal_injective e1).symm

theorem restrictNormal_infiniteLocalSymbol_norm (v' : InfinitePlace K') (a : v'.Completionˣ) :
    ((infiniteLocalSymbol L' v' a).restrictScalars K).restrictNormal L =
      infiniteLocalSymbol L (v'.comap (algebraMap K K'))
        (LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a) := by
  by_cases hv' : v'.IsReal
  · have hv := hv'.comap (algebraMap K K')
    obtain ⟨u'⟩ := IdeleNorm.nonempty_infinitePlacesOver L' v'
    have hu'v' : (u' : InfinitePlace L').comap (algebraMap K' L') = v' :=
      (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq v' _).1 u'.2
    have hu : ((u' : InfinitePlace L').comap (algebraMap L L')).LiesOver
        (v'.comap (algebraMap K K')) :=
      (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq _ _).2 (by
        rw [← comap_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq K K' L',
          comap_comp, hu'v'])
    rw [infiniteLocalSymbol_apply L' v' hv' u', infiniteLocalSymbol_apply L _ hv ⟨_, hu⟩,
      extensionEmbeddingOfIsReal_normUnits v' hv' a]
    split_ifs
    · exact restrictNormal_restrictScalars_conjAt (u' : InfinitePlace L') (by rw [hu'v']; exact hv')
    · exact restrictNormal_restrictScalars_one
  · rw [infiniteLocalSymbol_of_not_isReal L' v' hv', MonoidHom.one_apply,
      restrictNormal_restrictScalars_one]
    by_cases hv : (v'.comap (algebraMap K K')).IsReal
    · obtain ⟨u⟩ := IdeleNorm.nonempty_infinitePlacesOver L (v'.comap (algebraMap K K'))
      rw [infiniteLocalSymbol_apply L _ hv u, if_neg]
      rw [not_lt, LocalField.coe_normUnits, GroundTheory.Global.InfinitePlace.extensionEmbeddingOfIsReal_norm
        hv (not_isReal_iff_isComplex.1 hv')]
      exact Complex.normSq_nonneg _
    · rw [infiniteLocalSymbol_of_not_isReal L _ hv, MonoidHom.one_apply]

end

end GroundTheory.Global
