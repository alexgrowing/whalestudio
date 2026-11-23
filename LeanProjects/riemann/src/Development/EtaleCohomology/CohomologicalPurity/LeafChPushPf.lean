import Development.EtaleCohomology.CohomologicalPurity.LeafRelPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

section
variable (R : Type) [CommRing R]

instance pcFreeP : PreservesColimitsOfShape WalkingSpan (freeP R) := by
  have : PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1} R)) :=
    (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} R)) :=
    inferInstance
  unfold freeP; infer_instance

instance pcFree : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free; infer_instance

instance pcWhisk : PreservesColimitsOfShape WalkingSpan ((SimplicialObject.whiskering _ _).obj (free R)) := by
  unfold SimplicialObject.whiskering; infer_instance

instance preservesSpanColimitsFaceMapComplex : PreservesColimitsOfShape WalkingSpan (AlgebraicTopology.alternatingFaceMapComplex (Shv R)) := by
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n => ?_)
  have e : AlgebraicTopology.alternatingFaceMapComplex (Shv R) ⋙ HomologicalComplex.eval _ _ n ≅
      (evaluation _ _).obj (op (SimplexCategory.mk n)) :=
    NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
      dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  exact preservesColimitsOfShape_of_natIso e.symm

instance pcExt : PreservesColimitsOfShape WalkingSpan
    (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) := by
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i => ?_)
  by_cases h : ∃ j, ComplexShape.embeddingDownNat.f j = i
  · obtain ⟨j, hj⟩ := h
    have e : ComplexShape.embeddingDownNat.extendFunctor (Shv R) ⋙ HomologicalComplex.eval _ _ i ≅
        HomologicalComplex.eval _ _ j :=
      NatIso.ofComponents (fun K => K.extendXIso _ hj) (fun f => by
        change (HomologicalComplex.extendMap f _).f i ≫ _ = _ ≫ f.f j
        rw [HomologicalComplex.extendMap_f _ _ hj]; simp)
    exact preservesColimitsOfShape_of_natIso e.symm
  · refine Functor.preservesColimitsOfShape_of_isZero _ ?_ _
    rw [Functor.isZero_iff]
    intro K
    exact K.isZero_extend_X _ i (fun j hj => h ⟨j, hj⟩)

instance pcChains : PreservesColimitsOfShape WalkingSpan (chains R) := by
  unfold chains chainsN; infer_instance

end

theorem LeafChPush_of : LeafChPush := by
  intro q P
  have h : IsPushout P.hom P.hom (dbl.inl P) (dbl.inr P) := IsPushout.of_hasPushout _ _
  exact (chains (ZMod q)).map_isPushout h

end LateralTheory.CohomologicalPurity.TubeCut
