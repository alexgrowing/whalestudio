import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ExceptionalMonomialOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CoordinateSubspaceIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponentsFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPartAlongDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplittingFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplittingUniqueness
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyBoundedOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure MonomialCaseHypotheses : Prop where
  card_lt_dim :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        (intersectionComponents T.boundary J).Nonempty → J.card < krullDimSucc T.scheme
  center_smooth :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            AlgebraicGeometry.Smooth
              ((componentUnionIdeal T.boundary J 𝒞 hop).subschemeι ≫ T.structMap)
  center_snc :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J 𝒞 hop) T.boundary
  blowup_total_transform :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary, ∀ (x' : ↥X'),
                ∃ (U' : X'.Opens) (ε : ℕ),
                  x' ∈ U' ∧ (ε = 0 ∨ ε = 1) ∧
                    (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
                      (Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme) ⊆
                        (D.support : Set ↥T.scheme)) ∧
                    (D.comap π).comap U'.ι =
                      (Blowup.strictTransform π Z D).comap U'.ι *
                        (Blowup.exceptionalIdeal π Z).comap U'.ι ^ ε
  components_subset_divisor_iff :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ C ∈ intersectionComponents T.boundary J,
          ∀ (i : Fin T.boundary.length),
            C ⊆ ((T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J
  transformed_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞))
            (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                    (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                    (Finset.image
                      (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ (ξ' : ↥X'), IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              ((Blowup.exceptionalIdeal π
                                (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                                  Set ↥X')) ∧
                            ∀ (ξ : ↥T.scheme), IsGenericPoint ξ C → π ξ' = ξ
  stratum_smooth :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap)
  orderAt_comap_off_exceptional :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData),
        Blowup.IsBlowupAlongIdealSheaf π Z →
          ∀ x' ∉ (Blowup.exceptionalIdeal π Z).support,
            ∀ (A : T.scheme.IdealSheafData), orderAt (A.comap π) x' = orderAt A (π x')
  orderAt_boundary_eq_one :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ D ∈ T.boundary, ∀ x ∈ D.support, orderAt D x = 1

theorem monomialGeometryHypotheses_of_monomialCaseHypotheses (hR : MonomialCaseHypotheses.{u}) :
    MonomialGeometryHypotheses.{u} where
  card_lt_dim := hR.card_lt_dim
  flat_comap_center := by
    intro T hT Y k' hk q g hg hT' J 𝒞 h𝒞 hop
    exact FunctorialResolution.EmbeddedResolution.comap_componentUnionIdeal_of_flat T hT Y k' q g hT' J 𝒞 h𝒞 hop
  center_smooth := hR.center_smooth
  center_snc := hR.center_snc
  center_support := by
    intro T hT J 𝒞 h𝒞 hop
    exact FunctorialResolution.EmbeddedResolution.componentUnionIdeal_support_eq_sUnion T hT J 𝒞 h𝒞 hop
  blowup_total_transform := hR.blowup_total_transform
  flat_components_down := by
    intro T hT Y k' hk q g hg hT' J C' hC'
    exact FunctorialResolution.EmbeddedResolution.exists_intersectionComponents_mapsTo_of_flat T hT Y k' q g hT' J C' hC'
  flat_components_up := by
    intro T hT Y k' hk q g hg hT' J C hC y hy
    exact FunctorialResolution.EmbeddedResolution.exists_mem_intersectionComponents_pullbackOverField_of_flat T hT Y k' q g hT' J C hC y hy
  smooth_components_down := by
    intro T hT Y q h hsm hq hV J C' hC'
    have : AlgebraicGeometry.Flat h := inferInstance
    have hV' : (T.pullbackOverField Y T.base q h).IsAdmissible := by
      rw [MarkedIdealWithBoundary.pullbackOverField_eq_pullbackAlong]
      exact hV
    have e : pullbackOverFieldIndex T Y T.base q h = pullbackAlongIndex T Y q h := by
      funext j
      apply Fin.ext
      rw [pullbackOverFieldIndex_val, pullbackAlongIndex_val]
    have hC'' : C' ∈ intersectionComponents (T.pullbackOverField Y T.base q h).boundary
        (Finset.image (pullbackOverFieldIndex T Y T.base q h) J) := by
      rw [e]
      exact hC'
    exact FunctorialResolution.EmbeddedResolution.exists_intersectionComponents_mapsTo_of_flat T hT Y T.base q h hV' J C' hC''
  smooth_components_up := by
    intro T hT Y q h hsm hq hV J C hC y hy
    have : AlgebraicGeometry.Flat h := inferInstance
    have hV' : (T.pullbackOverField Y T.base q h).IsAdmissible := by
      rw [MarkedIdealWithBoundary.pullbackOverField_eq_pullbackAlong]
      exact hV
    have e : pullbackOverFieldIndex T Y T.base q h = pullbackAlongIndex T Y q h := by
      funext j
      apply Fin.ext
      rw [pullbackOverFieldIndex_val, pullbackAlongIndex_val]
    obtain ⟨C', hC'mem, hyC', hgen⟩ :=
      FunctorialResolution.EmbeddedResolution.exists_mem_intersectionComponents_pullbackOverField_of_flat T hT Y T.base q h hV' J C hC y hy
    refine ⟨C', ?_, hyC', hgen⟩
    rw [← e]
    exact hC'mem
  components_disjoint := by
    intro T hT J C hC C' hC' hne
    exact FunctorialResolution.EmbeddedResolution.intersectionComponents_disjoint_of_smooth T J (hR.stratum_smooth T hT J) C C' hC hC' hne
  components_finite := by
    intro T hT J
    exact FunctorialResolution.EmbeddedResolution.intersectionComponents_finite T hT J
  components_subset_divisor_iff := hR.components_subset_divisor_iff
  transformed_components := hR.transformed_components
  level_schemeDim_le := by
    intro T hT s i hi
    have h := MarkedIdealWithBoundary.transformAt_dim_le FunctorialResolution.EmbeddedResolution.dimensionNonincreasingAlongBlowups hT s i hi
    rwa [MarkedIdealWithBoundary.transformAt_dim] at h
  stratum_smooth := hR.stratum_smooth
  level_valid := by
    intro T hT s i hi
    exact MarkedIdealWithBoundary.IsAdmissible.transformAt FunctorialResolution.EmbeddedResolution.effectiveCartierSupportContainsNoComponent hT s i hi
  orderAt_bounded := by
    intro T hT I hI
    exact FunctorialResolution.EmbeddedResolution.exists_orderAt_le T hT I hI
  orderAt_comap_off_exceptional := hR.orderAt_comap_off_exceptional
  orderAt_boundary_eq_one := hR.orderAt_boundary_eq_one
  sUnion_isOpen := by
    intro T hT J 𝒞 h𝒞
    exact FunctorialResolution.EmbeddedResolution.isOpen_preimage_sUnion_intersectionComponents T hT J (hR.stratum_smooth T hT J) 𝒞 h𝒞
  withBoundary_valid := by
    intro T hT E' hE
    apply MarkedIdealWithBoundary.validOfSameNontrivialBoundary <;> assumption

structure OrderReductionHypotheses : Prop where
  controlledTransform_orderAt_le :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
                (∀ x ∈ Z.support, orderAt J x = (c : ℕ∞)) →
                  ∀ (J' : X'.IdealSheafData),
                    Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
                      ∀ x' ∈ (Blowup.exceptionalIdeal π Z).support, orderAt J' x' ≤ (c : ℕ∞)
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)
  monomial : MonomialCaseHypotheses.{u}

theorem geometricHypotheses_of_orderReductionHypotheses (hR : OrderReductionHypotheses.{u}) : PrincipalizationGeometryHypotheses.{u} where
  maxContactTransport := FunctorialResolution.EmbeddedResolution.isoInvariantOrderCertificateDescend
  exceptional_components_not_subset := by
    intro T hT Z hZsm hZsnc X' π hπ J c hord J' htr C' hC'
    have := hT.charZero
    have := hT.smooth
    have := hT.isNoetherian
    have := FunctorialResolution.EmbeddedResolution.isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ
    refine FunctorialResolution.EmbeddedResolution.controlledTransform_not_subset_support T.structMap Z T.boundary hZsnc π hπ
      J c hord J' htr C' hC'.1 hC'.2.1 ?_
    intro S hirr hsub hsup
    exact hC'.2.2 S hirr hsup hsub
  orderAt_baseChange := by
    intro T hT L hL hLz f I y
    have := hT.charZero
    have := hT.smooth
    exact FunctorialResolution.EmbeddedResolution.orderAt_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) I y
  controlledTransform_orderAt_le := hR.controlledTransform_orderAt_le
  splitting_baseChange := by
    intro T hT L hL hLz f hV M N hs
    exact FunctorialResolution.EmbeddedResolution.isMonomialSplitting_comap_of_flat
      (CategoryTheory.Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f)) hs
  splitting_smooth_pullback := by
    intro T hT Y q h hsm hq hV M N hs
    exact FunctorialResolution.EmbeddedResolution.isMonomialSplitting_comap_of_smooth h hs
  splitting_exists := by
    intro T hT
    have := hT.charZero
    have := hT.smooth
    have := hT.locallyOfFiniteType
    have := hT.quasiCompact
    have := hT.isNoetherian
    exact FunctorialResolution.EmbeddedResolution.exists_isMonomialSplitting T.structMap T.boundary hT.snc T.ideal
      hT.nonzeroOnComponents
  splitting_unique := by
    intro T hT M N M' N' hs hs'
    have := hT.charZero
    have := hT.smooth
    have := hT.locallyOfFiniteType
    have := hT.quasiCompact
    have := hT.isNoetherian
    exact FunctorialResolution.EmbeddedResolution.isMonomialSplitting_unique T.structMap T.boundary hT.snc
      hT.nonzeroOnComponents hs hs'
  strictTransform_components := hR.strictTransform_components
  monomialInputs := monomialGeometryHypotheses_of_monomialCaseHypotheses hR.monomial

end FunctorialResolution.EmbeddedResolution

end
