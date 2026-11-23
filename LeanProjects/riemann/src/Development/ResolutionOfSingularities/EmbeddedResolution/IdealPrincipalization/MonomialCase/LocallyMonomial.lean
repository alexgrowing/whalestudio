import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

def IsMonomialNear {X : Scheme.{u}} (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (x : ↥X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
    M.comap U.ι =
      (List.ofFn (fun i : Fin E.length => (E.get i).comap U.ι ^ a i)).foldr (· * ·) ⊤

structure IsLocallyMonomialTriple (T : MarkedIdealWithBoundary.{u}) : Prop where
  valid : T.IsAdmissible
  monomialNear : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, IsMonomialNear T.boundary T.ideal x

structure IsLocallyMonomialPrincipalization (P : ℕ → Prop) (F : PrincipalizationAssignment.{u}) : Prop where
  center_subset_boundaryLocus :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length,
        (↑((F T).center i).support : Set ↥((F T).schemeAt i)) ⊆
          MarkedSequenceOfBlowups.boundaryLocus (F T) i
  cert :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length,
        PrincipalizationCertificate ((F T).schemeAt i) (MarkedSequenceOfBlowups.projectionToSpec (F T) i) ((F T).ideal i) T.mult
          (MarkedSequenceOfBlowups.boundaryLocus (F T) i) ((F T).center i)
  base_change :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
        (E' : List (T.baseChange L f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
          IsLocallyMonomialTriple ((T.baseChange L f).withBoundary E') →
            P ((T.baseChange L f).withBoundary E').krullDimSucc →
              IsPullbackBlowupSequence
                (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))
                (F ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (F T).toSequenceOfBlowups
  base_change_strict :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
        (E' : List (T.baseChange L f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E' →
          IsLocallyMonomialTriple ((T.baseChange L f).withBoundary E') →
            P ((T.baseChange L f).withBoundary E').krullDimSucc →
              IsStrictPullbackBlowupSeq
                (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))
                (F ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups (F T).toSequenceOfBlowups
  center_eq :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length,
        (F T).center i = monomialCenter ((F T).ideal i) T.mult ((F T).boundary i)
  minLevel_ne_zero :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length, minIndexCard ((F T).ideal i) T.mult ((F T).boundary i) ≠ 0
  key_le :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ t, t + 1 < (F T).length →
        (centerInvariant ((F T).ideal t) T.mult ((F T).boundary t)).Le
          (centerInvariant ((F T).ideal (t + 1)) T.mult ((F T).boundary (t + 1)))
  monomial_near :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i ≤ (F T).length, ∀ x ∈ orderAtLeastLocus ((F T).ideal i) T.mult,
        IsMonomialNear ((F T).boundary i) ((F T).ideal i) x
  center_nonempty :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ i < (F T).length, (↑((F T).center i).support : Set ↥((F T).schemeAt i)).Nonempty
  resolves :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      MarkedSequenceOfBlowups.IsResolution (F T)
  smooth_pullback :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
            IsLocallyMonomialTriple ((T.pullbackAlong Y q h).withBoundary E') →
              P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
                IsPullbackBlowupSequence h
                  (F ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups (F T).toSequenceOfBlowups
  smooth_pullback_strict :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Surjective h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
            IsLocallyMonomialTriple ((T.pullbackAlong Y q h).withBoundary E') →
              P ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc →
                IsStrictPullbackBlowupSeq h
                  (F ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups (F T).toSequenceOfBlowups
  trivial_of_coSupport_empty :
    ∀ (T : MarkedIdealWithBoundary.{u}), IsLocallyMonomialTriple T → P T.krullDimSucc →
      orderAtLeastLocus T.ideal T.mult = ∅ → (F T).length = 0

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
