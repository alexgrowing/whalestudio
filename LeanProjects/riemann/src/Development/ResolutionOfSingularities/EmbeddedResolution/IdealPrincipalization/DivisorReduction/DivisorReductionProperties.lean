import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.UntwistedDivisorRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure DivisorReductionProperties (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) : Prop where
  isMarked_pushedTop :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                      (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
                  T.structMap T.ideal T.mult T.boundary
  isMarked_pushedPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                        (DivisorReduction.ambientBlowupSeq hres hno T j hj
                          (DivisorReduction.lowerIdealAfterBlowup T j hj)
                          (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
                    T.structMap T.ideal T.mult T.boundary
  valid_lowerPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ → (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible
  orderAt_ctrlIdeal_le_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                ∀ i ≤ s.length,
                  ∀ (x : ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj
                            (DivisorReduction.lowerIdealWithoutBlowup T)
                            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).obj i)),
                    orderAt ((DivisorReduction.ambientBlowupSeq hres hno T j hj
                          (DivisorReduction.lowerIdealWithoutBlowup T)
                          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
                        T.ideal T.mult i) x ≤ (T.mult : ℕ∞)
  orderAt_ctrlIdeal_le_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  ∀ i ≤ s.length + 1,
                    ∀ (x : ↥((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                              (DivisorReduction.ambientBlowupSeq hres hno T j hj
                                (DivisorReduction.lowerIdealAfterBlowup T j hj)
                                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).obj i)),
                      orderAt ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                            (DivisorReduction.ambientBlowupSeq hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
                          T.ideal T.mult i) x ≤ (T.mult : ℕ∞)
  coSupport_inter_ker_eq_empty_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                orderAtLeastLocus (s.ideal s.length) T.mult = ∅ →
                  orderAtLeastLocus ((DivisorReduction.ambientBlowupSeq hres hno T j hj
                          (DivisorReduction.lowerIdealWithoutBlowup T)
                          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
                        T.ideal T.mult s.length) T.mult ∩
                      ↑(AlgebraicGeometry.Scheme.Hom.ker
                          (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                            (DivisorReduction.lowerIdealWithoutBlowup T)
                            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr s.length)).support = ∅
  coSupport_inter_ker_eq_empty_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  orderAtLeastLocus (s.ideal s.length) T.mult = ∅ →
                    orderAtLeastLocus ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                            (DivisorReduction.ambientBlowupSeq hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
                          T.ideal T.mult (s.length + 1)) T.mult ∩
                        (((AlgebraicGeometry.Scheme.Hom.ker
                            (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr s.length)).support :
                          Set ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr).obj s.length))) = ∅
  isPullbackSeq_ambientTower :
    ∀ (X Y S S' : AlgebraicGeometry.Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X) (ψ : S' ⟶ S)
      [AlgebraicGeometry.IsClosedImmersion σ] [AlgebraicGeometry.IsClosedImmersion σ']
      [AlgebraicGeometry.Flat φ] [AlgebraicGeometry.IsNoetherian X]
      [AlgebraicGeometry.IsNoetherian Y],
      CategoryTheory.IsPullback σ' ψ φ σ →
        ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent) (hc' : d'.CentersContainNoComponent),
          IsPullbackBlowupSequence ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
            IsPullbackBlowupSequence φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
              (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  isStrictPullbackSeq_ambientTower :
    ∀ (X Y S S' : AlgebraicGeometry.Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X) (ψ : S' ⟶ S)
      [AlgebraicGeometry.IsClosedImmersion σ] [AlgebraicGeometry.IsClosedImmersion σ']
      [AlgebraicGeometry.Flat φ] [AlgebraicGeometry.IsNoetherian X]
      [AlgebraicGeometry.IsNoetherian Y],
      CategoryTheory.IsPullback σ' ψ φ σ →
        ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent) (hc' : d'.CentersContainNoComponent),
          IsStrictPullbackBlowupSeq ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
            IsStrictPullbackBlowupSeq φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
              (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  comap_ctrlIdeal_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                ∀ i ≤ s.length,
                  ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
                        T.ideal T.mult i).comap
                      (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                        (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr i) = s.ideal i
  comap_ctrlIdeal_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  ∀ i ≤ s.length,
                    ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                              (DivisorReduction.ambientBlowupSeq hres hno T j hj
                                (DivisorReduction.lowerIdealAfterBlowup T j hj)
                                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
                          T.ideal T.mult (i + 1)).comap
                        (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                          (DivisorReduction.lowerIdealAfterBlowup T j hj)
                          (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr i) = s.ideal i
  preIdeal_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L),
        (T.baseChange L f).IsAdmissible →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hj' : j < (T.baseChange L f).boundary.length),
            DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
              (DivisorReduction.containedComponentsIdeal T j hj).comap
                (CategoryTheory.Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  preIdeal_pullbackAlong :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : AlgebraicGeometry.Scheme.{u})
        (q : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h],
        CategoryTheory.CategoryStruct.comp h T.structMap = q →
          (T.pullbackAlong Y q h).IsAdmissible →
            ∀ (j : ℕ) (hj : j < T.boundary.length)
              (hj' : j < (T.pullbackAlong Y q h).boundary.length),
              DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
                (DivisorReduction.containedComponentsIdeal T j hj).comap h
  preIdeal_eq_top_of_imageIdeal :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length)
        (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData),
        T.mult = 1 →
          (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
                (CategoryTheory.CategoryStruct.comp (T.boundary.get ⟨j, hj⟩).subschemeι
                  T.structMap) J
                (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
                  (T.boundary.eraseIdx j))).IsAdmissible →
            T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J →
              DivisorReduction.containedComponentsIdeal T j hj = ⊤

theorem DivisorReductionProperties.toDivisorReductionStepProperties {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} (h : DivisorReductionProperties hres hno) :
    DivisorReductionStepProperties hres hno :=
  { exists_ideal_mul_preIdeal_pow := fun T hV _ j hj =>
      exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
    isMarked_pushedTop := h.isMarked_pushedTop
    isMarked_pushedPre := h.isMarked_pushedPre
    isBlowup_id_preIdeal := fun T hV j hj => isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV j hj
    valid_lowerTop := fun T hV hOB hbal j hj hZ =>
      DivisorReduction.isAdmissible_restrictToDivisor T hV hOB hbal j hj hZ
    valid_lowerPre := h.valid_lowerPre
    orderAt_ctrlIdeal_le_top := h.orderAt_ctrlIdeal_le_top
    orderAt_ctrlIdeal_le_pre := h.orderAt_ctrlIdeal_le_pre
    coSupport_inter_ker_eq_empty_top := h.coSupport_inter_ker_eq_empty_top
    coSupport_inter_ker_eq_empty_pre := h.coSupport_inter_ker_eq_empty_pre
    isPullbackSeq_ambientTower := h.isPullbackSeq_ambientTower
    isStrictPullbackSeq_ambientTower := h.isStrictPullbackSeq_ambientTower
    comap_ctrlIdeal_top := h.comap_ctrlIdeal_top
    comap_ctrlIdeal_pre := h.comap_ctrlIdeal_pre
    preIdeal_baseChange := h.preIdeal_baseChange
    preIdeal_pullbackAlong := h.preIdeal_pullbackAlong
    preIdeal_eq_top_of_imageIdeal := h.preIdeal_eq_top_of_imageIdeal
    smooth_preIdeal := fun T hV j hj => smooth_subschemeι_containedComponentsIdeal_comp T hV j hj
    hasSNCWith_preIdeal := fun T hV j hj => hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj
    support_preIdeal_subset := fun T hV j hj => support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj }

end FunctorialResolution.EmbeddedResolution

end
