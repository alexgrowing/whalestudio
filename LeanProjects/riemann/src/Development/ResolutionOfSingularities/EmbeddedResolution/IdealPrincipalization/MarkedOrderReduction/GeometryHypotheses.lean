import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.InvarianceUnderIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure PrincipalizationGeometryHypotheses : Prop where
  maxContactTransport : OrderCertificateIsoInvariantOfMaxContact.{u}
  exceptional_components_not_subset : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
    ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
      (∀ x : ↥T.scheme, x ∈ Z.support → orderAt J x = (c : ℕ∞)) →
    ∀ J' : X'.IdealSheafData,
      Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
    ∀ C' : Set ↥X', IsIrreducibleComponentOf C' (↑(Blowup.exceptionalIdeal π Z).support : Set ↥X') →
      ¬ C' ⊆ (↑J'.support : Set ↥X')
  orderAt_baseChange : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (I : T.scheme.IdealSheafData) (y : ↥(T.baseChange L f).scheme),
      orderAt (I.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f))) y =
        orderAt I ((pullback.fst T.structMap (specMapOfFieldHom T.base L f)).base y)
  controlledTransform_orderAt_le : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
    ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
      (∀ x : ↥T.scheme, x ∈ Z.support → orderAt J x = (c : ℕ∞)) →
    ∀ J' : X'.IdealSheafData,
      Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
    ∀ x' : ↥X', x' ∈ (Blowup.exceptionalIdeal π Z).support → orderAt J' x' ≤ (c : ℕ∞)
  splitting_baseChange : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L),
      (T.baseChange L f).IsAdmissible →
    ∀ M N : T.scheme.IdealSheafData,
      IsMonomialSplitting T.boundary T.ideal M N →
      IsMonomialSplitting (T.baseChange L f).boundary (T.baseChange L f).ideal
        (M.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
        (N.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
  splitting_smooth_pullback : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
      (T.pullbackAlong Y q h).IsAdmissible →
    ∀ M N : T.scheme.IdealSheafData,
      IsMonomialSplitting T.boundary T.ideal M N →
      IsMonomialSplitting (T.pullbackAlong Y q h).boundary (T.pullbackAlong Y q h).ideal
        (M.comap h) (N.comap h)
  splitting_exists : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∃ M N : T.scheme.IdealSheafData, IsMonomialSplitting T.boundary T.ideal M N
  splitting_unique : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ M N M' N' : T.scheme.IdealSheafData,
      IsMonomialSplitting T.boundary T.ideal M N →
      IsMonomialSplitting T.boundary T.ideal M' N' →
      M = M' ∧ N = N'
  strictTransform_components : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
    ∀ D ∈ T.boundary,
    ∀ C' : Set ↥X', IsIrreducibleComponentOf C' (↑(Blowup.strictTransform π Z D).support : Set ↥X') →
      ∃ (η' : ↥X') (C : Set ↥T.scheme),
        C' = closure {η'} ∧
        η' ∉ (Blowup.exceptionalIdeal π Z).support ∧
        IsIrreducibleComponentOf C (↑D.support : Set ↥T.scheme) ∧
        ¬ C ⊆ (↑Z.support : Set ↥T.scheme) ∧
        C = closure {π.base η'}
  monomialInputs : MonomialGeometryHypotheses.{u}

end FunctorialResolution.EmbeddedResolution

end
