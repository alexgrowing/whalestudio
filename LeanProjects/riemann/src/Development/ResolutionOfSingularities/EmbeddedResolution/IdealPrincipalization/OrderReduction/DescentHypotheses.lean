import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

@[reducible] def lowerDimensionalFamily (A : ℕ → PrincipalizationAssignment.{u}) (T : MarkedIdealWithBoundary.{u}) :
    ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups :=
  fun S _ j => A j S

noncomputable def maxContactPrincipalization (hinv : ComapIsoInvariance.{u}) (A : ℕ → PrincipalizationAssignment.{u}) :
    PrincipalizationAssignment.{u} :=
  fun T => MaxContactReduction.reduceOrder hinv T (lowerDimensionalFamily A T)

@[simp] theorem maxContactPrincipalization_apply (hinv : ComapIsoInvariance.{u}) (A : ℕ → PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) :
    maxContactPrincipalization hinv A T = MaxContactReduction.reduceOrder hinv T (lowerDimensionalFamily A T) := rfl

structure OrderReductionHypotheses (P : ℕ → Prop) (T : MarkedIdealWithBoundary.{u}) : Prop where
  dim_prop : P T.krullDimSucc
  orderLE : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)
  coSupport_nonempty : (orderAtLeastLocus T.ideal T.mult).Nonempty
  valid : T.IsAdmissible

theorem OrderReductionHypotheses.orderAtLeastLocus_ne_empty {P : ℕ → Prop} {T : MarkedIdealWithBoundary.{u}} (h : OrderReductionHypotheses P T) :
    orderAtLeastLocus T.ideal T.mult ≠ ∅ :=
  h.coSupport_nonempty.ne_empty

def IsLocalIsomorphism {W' W : Scheme.{u}} (g : W' ⟶ W) : Prop :=
  ∀ x : ↥W', ∃ U : W'.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ g)

noncomputable abbrev coverBlowupSequence (hinv : ComapIsoInvariance.{u}) (A : ℕ → PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    MarkedBlowupSequenceData (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.coverTriple T hv).mult
      (MaxContactCoverData.coverTriple T hv).boundary :=
  MaxContactCoverData.coverMarkedBlowupData T hv hinv (lowerDimensionalFamily A T)

structure CoverSequenceProperties (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) : Prop where
  center_ne_top : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
    ∀ i < (coverBlowupSequence hinv A T h.valid).length,
      (coverBlowupSequence hinv A T h.valid).center i ≠ ⊤
  cert : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T), T.mult = 1 →
    ∀ i < (coverBlowupSequence hinv A T h.valid).length,
      OrderCertificate ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.schemeAt i)
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.projectionToBase i ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap)
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.ideal i) 1
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.boundaryLocus i)
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.center i)
  descends : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups
  hypersurface : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T), T.boundary = [] → T.mult = 1 →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
      [AlgebraicGeometry.IsClosedImmersion e], e ≫ T.structMap = q →
      IsSmoothDivisor T.structMap (Scheme.Hom.ker e) →
    ∀ J : Y.IdealSheafData,
      (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData)).IsAdmissible →
      T.ideal = imageIdealSheaf e J →
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups
        (A 0 (T.withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups
  resolves : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
    orderAtLeastLocus ((coverBlowupSequence hinv A T h.valid).ideal (coverBlowupSequence hinv A T h.valid).length)
      (MaxContactCoverData.tunedMult T) = ∅

structure DescentHypotheses (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u}) : Prop where
  tuning : IsMarkedIffBalancedTunedSheaf.{u}
  cert_descend : ∀ (k : Type u) [Field k] (W' W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (g : W' ⟶ W),
      IsLocalIsomorphism g → AlgebraicGeometry.Surjective g →
    ∀ (N : W.IdealSheafData) (μ : ℕ) (Mem : Set ↥W) (Z : W.IdealSheafData),
      OrderCertificate W' (g ≫ p) (N.comap g) μ (g.base ⁻¹' Mem) (Z.comap g) →
      OrderCertificate W p N μ Mem Z
  base_change : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      (∀ x : ↥((T.baseChange L f).withBoundary E').scheme,
        orderAt ((T.baseChange L f).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (maxContactPrincipalization hinv A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  base_change_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.baseChange L f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
      ((T.baseChange L f).withBoundary E').IsAdmissible →
      P ((T.baseChange L f).withBoundary E').krullDimSucc →
      (∀ x : ↥((T.baseChange L f).withBoundary E').scheme,
        orderAt ((T.baseChange L f).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (maxContactPrincipalization hinv A ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  comp_openImmersion : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme)
      (D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
      (i : ℕ) (hi : i ≤ (coverBlowupSequence hinv A T h.valid).length),
      IsLocalIsomorphism
        (D.comp i ((coverBlowupSequence hinv A T h.valid).le_toSequenceOfBlowups_length hi))
  locallyNoetherian : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme),
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups →
      (∀ i ≤ d.length, IsLocallyNoetherian (d.obj i)) ∧
      (∀ i ≤ (coverBlowupSequence hinv A T h.valid).length,
        IsLocallyNoetherian ((coverBlowupSequence hinv A T h.valid).obj i))
  isMarked : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme),
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups →
      d.IsMarked T.structMap (MaxContactCoverData.balancedTunedIdeal T h.valid)
        (MaxContactCoverData.tunedMult T) T.boundary
  isMarked_of_trim : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (d : BlowupSequenceData T.scheme) (I : T.scheme.IdealSheafData) (m : ℕ),
      d.IsMarked T.structMap I m (MaxContactReduction.dropTrivialBoundary T).boundary →
      d.IsMarked T.structMap I m T.boundary
  order_le : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.length →
      ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (T.mult : ℕ∞)
  smooth_pullback : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (g : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth g], g ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q g).boundary E' →
      ((T.pullbackAlong Y q g).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q g).withBoundary E').krullDimSucc →
      (∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) →
      IsPullbackBlowupSequence g
        (maxContactPrincipalization hinv A ((T.pullbackAlong Y q g).withBoundary E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (g : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth g] [AlgebraicGeometry.Surjective g], g ≫ T.structMap = q →
    ∀ E' : List Y.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q g).boundary E' →
      ((T.pullbackAlong Y q g).withBoundary E').IsAdmissible →
      P ((T.pullbackAlong Y q g).withBoundary E').krullDimSucc →
      (∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) →
      IsStrictPullbackBlowupSeq g
        (maxContactPrincipalization hinv A ((T.pullbackAlong Y q g).withBoundary E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  flat_coverMap : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
      AlgebraicGeometry.Flat (MaxContactCoverData.coverMap T h.valid)
  surjective_coverMap : ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
      AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap T h.valid)
  valid_subst_ker : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
      [AlgebraicGeometry.IsClosedImmersion e], e ≫ T.structMap = q →
    ∀ J : Y.IdealSheafData, (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData)).IsAdmissible →
    ∀ (ε : Y ⟶ (Scheme.Hom.ker e).subscheme),
      ε ≫ (Scheme.Hom.ker e).subschemeι = e →
      (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
          ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) (imageIdealSheaf ε J)
          ([] : List (Scheme.Hom.ker e).subscheme.IdealSheafData)).IsAdmissible ∧
      (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
          ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) (imageIdealSheaf ε J)
          ([] : List (Scheme.Hom.ker e).subscheme.IdealSheafData)).krullDimSucc =
        (T.withSchemeIdealBoundary Y q J ([] : List Y.IdealSheafData)).krullDimSucc
  tunedIdeal_of_mult_one : ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible), T.mult = 1 →
      MaxContactCoverData.balancedTunedIdeal T hv = T.ideal
  valid_trim : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → (MaxContactReduction.dropTrivialBoundary T).IsAdmissible
  valid_withDivisor : ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → T.boundary = [] →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
      [AlgebraicGeometry.IsClosedImmersion e], e ≫ T.structMap = q →
      IsSmoothDivisor T.structMap (Scheme.Hom.ker e) →
      (T.withBoundary [Scheme.Hom.ker e]).IsAdmissible

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
