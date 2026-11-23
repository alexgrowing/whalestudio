import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsSmoothBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemoval
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IteratedStrictTransformPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.FaithfullyFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isPullback_of_length_eq_zero_of_length_eq_zero {X' X : Scheme.{u}} (φ : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    IsPullbackBlowupSequence φ t s := by
  refine isPullback_of_length_zero_of_comap_center_eq_top φ t s ht ?_
  intro i hi _ _
  exact absurd hi (by omega)

namespace MaxContactFunctoriality

def removeUnitIdeals {X : Scheme.{u}} (L : List X.IdealSheafData) : List X.IdealSheafData :=
  L.filter (fun D => @decide (D ≠ ⊤) (Classical.propDecidable _))

private theorem removeUnitIdeals_cons_top {X : Scheme.{u}}
    (L : List X.IdealSheafData) :
    removeUnitIdeals ((⊤ : X.IdealSheafData) :: L) = removeUnitIdeals L := by
  simp [removeUnitIdeals]

private theorem removeUnitIdeals_cons_of_ne_top {X : Scheme.{u}} {D : X.IdealSheafData}
    (hD : D ≠ ⊤) (L : List X.IdealSheafData) :
    removeUnitIdeals (D :: L) = D :: removeUnitIdeals L := by
  simp [removeUnitIdeals, hD]

theorem removeUnitIdeals_map_comap_removeUnitIdeals {X Y : Scheme.{u}} (f : Y ⟶ X) (L : List X.IdealSheafData) :
    removeUnitIdeals (List.map (fun D => D.comap f) (removeUnitIdeals L)) =
      removeUnitIdeals (List.map (fun D => D.comap f) L) := by
  induction L with
  | nil => rfl
  | cons D L ih =>
    by_cases hD : D = ⊤
    · subst hD
      rw [removeUnitIdeals_cons_top, ih]
      simp only [List.map_cons, Scheme.IdealSheafData.comap_top]
      rw [removeUnitIdeals_cons_top]
    · rw [removeUnitIdeals_cons_of_ne_top hD]
      simp only [List.map_cons]
      by_cases hD' : D.comap f = ⊤
      · rw [hD', removeUnitIdeals_cons_top, removeUnitIdeals_cons_top, ih]
      · rw [removeUnitIdeals_cons_of_ne_top hD', removeUnitIdeals_cons_of_ne_top hD', ih]

noncomputable abbrev smoothPullbackTriple (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) :
    MarkedIdealWithBoundary.{u} :=
  (S.pullbackAlong X' (q ≫ S.structMap) q).withBoundary
    (removeUnitIdeals (S.pullbackAlong X' (q ≫ S.structMap) q).boundary)

def LoopCompatibleWithSmoothPullback (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) : Prop :=
  ∀ (_hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (_hin : OrderReduction.OrderReductionHypotheses.{u})
    (_hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u})
    (_hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u}),
    (∀ a b : ℕ, a ≤ b → P b → P a) →
    ∀ B : PrincipalizationAssignment.{u}, (∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) →
      IsBoundaryPositionInvariant P A →
      ∀ T T' : MarkedIdealWithBoundary.{u}, P T.krullDimSucc → P T'.krullDimSucc →
        ∀ S : MarkedIdealWithBoundary.{u}, S.IsAdmissible →
          (∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) →
          S.krullDimSucc ≤ T.krullDimSucc →
          ∀ H : S.scheme.IdealSheafData,
            (∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType S.structMap],
                IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H) →
            InStrictNormalCrossingPosition S.structMap [H] →
            (∀ D ∈ S.boundary, D ≠ ⊤) →
            ∀ {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q],
              (smoothPullbackTriple S q).IsAdmissible →
              (smoothPullbackTriple S q).krullDimSucc ≤ T'.krullDimSucc →
              (∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType (smoothPullbackTriple S q).structMap],
                  IsMaxContactHypersurface (smoothPullbackTriple S q).base
                    (smoothPullbackTriple S q).structMap (smoothPullbackTriple S q).ideal
                    (smoothPullbackTriple S q).mult (H.comap q)) →
              InStrictNormalCrossingPosition (smoothPullbackTriple S q).structMap [H.comap q] →
              IsPullbackBlowupSequence q
                (MaxContactReduction.reduceAlongHypersurface hinv T' (lowerDimensionalFamily A T') (smoothPullbackTriple S q)
                  (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
                (MaxContactReduction.reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups

def TrivialOnEmptyOrderLocus (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) : Prop :=
  ∀ T : MarkedIdealWithBoundary.{u}, OrderReductionHypotheses P T →
    ∀ {Y : Scheme.{u}} (g : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth g] (t : SequenceOfBlowups Y),
      t.length = 0 →
      orderAtLeastLocus (T.ideal.comap g) T.mult = (∅ : Set ↥Y) →
      IsPullbackBlowupSequence g t (maxContactPrincipalization hinv A T).toSequenceOfBlowups

noncomputable abbrev dropTrivialBoundaryPullback (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (qY : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    (E' : List Y.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  ((MaxContactReduction.dropTrivialBoundary T).pullbackAlong Y qY h).withBoundary (removeUnitIdeals E')

theorem reduceAlongHypersurface_isomorphic_of_isMaxContactHypersurface
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (_hshift : IsBoundaryPositionInvariant P A)
    (hstar0 : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u})
    (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (T : MarkedIdealWithBoundary.{u}) (hP : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hv : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdim : S.krullDimSucc ≤ T.krullDimSucc)
    (H H' : S.scheme.IdealSheafData)
    (hH : ∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    (hH' : ∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H')
    (hH'snc : InStrictNormalCrossingPosition S.structMap [H']) :
    (MaxContactReduction.reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic
      (MaxContactReduction.reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H').toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hsmid : AlgebraicGeometry.Smooth (𝟙 S.scheme) := inferInstance
  have hflid : AlgebraicGeometry.Flat (𝟙 S.scheme) := inferInstance
  have hsuid : AlgebraicGeometry.Surjective (𝟙 S.scheme) := inferInstance
  have hft2 : AlgebraicGeometry.LocallyOfFiniteType S.structMap := hv.locallyOfFiniteType
  have hpb : LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme) = S := by
    simp [LowerDimReductionPullback.pullbackTriple, MarkedIdealWithBoundary.pullbackAlong]
  have hVpb : (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).IsAdmissible := by rw [hpb]; exact hv
  have hdimpb : (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).krullDimSucc ≤ T.krullDimSucc := by rw [hpb]; exact hdim
  have hHup : ∀ [inst : AlgebraicGeometry.LocallyOfFiniteType
      (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).structMap],
      IsMaxContactHypersurface (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).base
        (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).structMap
        (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).ideal
        (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).mult H := by
    intro inst
    exact isMaxContactHypersurface_of_triple_eq hpb inst hft2 H H HEq.rfl (@hH hft2)
  have hHupsnc : InStrictNormalCrossingPosition (LowerDimReductionPullback.pullbackTriple S (𝟙 S.scheme)).structMap [H] :=
    inStrictNormalCrossingPosition_of_triple_eq hpb [H] [H] HEq.rfl hHsnc
  have hA := BoundarySeparationBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar0 hin hMC hAdm hinv P hmono A B hspec
    T hP S hv hord hdim H hH hHsnc (𝟙 S.scheme) hVpb hdimpb H hHup hHupsnc
  have hB := BoundarySeparationBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar0 hin hMC hAdm hinv P hmono A B hspec
    T hP S hv hord hdim H' hH' hH'snc (𝟙 S.scheme) hVpb hdimpb H hHup hHupsnc
  exact hA.isomorphic_of_isomorphic hB (SequenceOfBlowups.isomorphic_refl _)

private theorem map_comap_map_comap {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : List Z.IdealSheafData) :
    List.map (fun D => D.comap f) (List.map (fun D => D.comap g) L)
      = List.map (fun D => D.comap (f ≫ g)) L := by
  rw [List.map_map]
  exact List.map_congr_left (fun D _ => (Scheme.IdealSheafData.comap_comp D f g).symm)

private theorem dropTrivialBoundary_boundary_eq_removeUnitIdeals (T : MarkedIdealWithBoundary.{u}) :
    (MaxContactReduction.dropTrivialBoundary T).boundary = removeUnitIdeals T.boundary := by
  rw [MaxContactReduction.dropTrivialBoundary_boundary]
  exact List.filter_congr (fun D _ => congrArg _ (Subsingleton.elim _ _))

private theorem removeUnitIdeals_eq_of_sameNontrivialBoundary {X : Scheme.{u}} {L L' : List X.IdealSheafData}
    (hL : MarkedIdealWithBoundary.SameNontrivialBoundary L L') : removeUnitIdeals L = removeUnitIdeals L' := by
  have hdn : ∀ D : X.IdealSheafData,
      (@decide (D ≠ ⊤) (Classical.propDecidable _))
        = !(@decide (D = ⊤) (Classical.propDecidable _)) :=
    fun D => @decide_not (D = ⊤) (Classical.propDecidable _) (Classical.propDecidable _)
  have hL' : List.filter (fun D : X.IdealSheafData =>
        !(@decide (D = ⊤) (Classical.propDecidable _))) L
      = List.filter (fun D : X.IdealSheafData =>
        !(@decide (D = ⊤) (Classical.propDecidable _))) L' := hL
  have h1 : removeUnitIdeals L = List.filter (fun D : X.IdealSheafData =>
      !(@decide (D = ⊤) (Classical.propDecidable _))) L :=
    List.filter_congr (fun D _ => hdn D)
  have h2 : List.filter (fun D : X.IdealSheafData =>
      !(@decide (D = ⊤) (Classical.propDecidable _))) L' = removeUnitIdeals L' :=
    List.filter_congr (fun D _ => (hdn D).symm)
  exact h1.trans (hL'.trans h2)

private theorem removeUnitIdeals_map_comap_congr {X Y : Scheme.{u}} (g : X ⟶ Y)
    {L L' : List Y.IdealSheafData}
    (hL : removeUnitIdeals L = removeUnitIdeals L') :
    removeUnitIdeals (List.map (fun D => D.comap g) L)
      = removeUnitIdeals (List.map (fun D => D.comap g) L') := by
  rw [← removeUnitIdeals_map_comap_removeUnitIdeals g L, ← removeUnitIdeals_map_comap_removeUnitIdeals g L', hL]

private theorem markedIdealWithBoundary_mk_congr {k : Type u} [fk : Field k] {Z : Scheme.{u}}
    {p₁ p₂ : Z ⟶ Spec (CommRingCat.of k)} {I₁ I₂ : Z.IdealSheafData} {m₁ m₂ : ℕ}
    {b₁ b₂ : List Z.IdealSheafData}
    (hp : p₁ = p₂) (hI : I₁ = I₂) (hm : m₁ = m₂) (hb : b₁ = b₂) :
    ({ base := k, instField := fk, scheme := Z, structMap := p₁, ideal := I₁, mult := m₁,
        boundary := b₁ } : MarkedIdealWithBoundary.{u}) =
      { base := k, instField := fk, scheme := Z, structMap := p₂, ideal := I₂, mult := m₂,
        boundary := b₂ } := by
  subst hp; subst hI; subst hm; subst hb; rfl

theorem smoothPullbackTriple_coverTriple_eq (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (qY : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h]
    (hq : h ≫ T.structMap = qY)
    (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y qY h).boundary E')
    (htrimv : (MaxContactReduction.dropTrivialBoundary T).IsAdmissible)
    (hpbv : (dropTrivialBoundaryPullback T qY h E').IsAdmissible)
    [AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv)]
    [AlgebraicGeometry.Surjective
      (Limits.pullback.fst (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))] :
    smoothPullbackTriple (MaxContactCoverData.coverTriple (dropTrivialBoundaryPullback T qY h E') hpbv)
        (Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) =
      smoothPullbackTriple (MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) htrimv)
        (Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) := by
  subst hq
  have hcond :
      Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
      = Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv := Limits.pullback.condition
  have hcond2 :
      (Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv) ≫ h
      = Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv :=
    (Category.assoc _ _ _).trans hcond
  have hti : MaxContactCoverData.balancedTunedIdeal (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv
      = (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap h := by
    have : AlgebraicGeometry.Smooth T.structMap := htrimv.smooth
    have : AlgebraicGeometry.LocallyOfFiniteType T.structMap := htrimv.locallyOfFiniteType
    have : AlgebraicGeometry.LocallyOfFiniteType (h ≫ T.structMap) := hpbv.locallyOfFiniteType
    exact balancedTunedSheaf_comap T.base T.structMap h T.ideal T.mult
  have hsmC := congrArg (fun φ => φ ≫ T.structMap) hcond2
  have hsm :
      Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫
          (h ≫ T.structMap))
      = Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv ≫ T.structMap) :=
    (Category.assoc _ _ _).symm.trans
      ((Category.assoc _ _ _).symm.trans (hsmC.trans (Category.assoc _ _ _)))
  have i1 := congrArg (fun J => (J.comap
      (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv)).comap
      (Limits.pullback.fst
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))) hti
  have i2 :
      (((MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap h).comap
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv)).comap
        (Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
      = (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap
        (Limits.pullback.fst
            (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)) :=
    (congrArg (fun J => J.comap
        (Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
      (Scheme.IdealSheafData.comap_comp
        (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv)
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv)
        h).symm).trans
      (Scheme.IdealSheafData.comap_comp
        (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv) _ _).symm
  have i3 := congrArg
      (fun φ => (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap φ) hcond
  have i4 :
      (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap
          (Limits.pullback.snd
              (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
              (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
            MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)
      = ((MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)).comap
        (Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) :=
    Scheme.IdealSheafData.comap_comp
      (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv) _ _
  have hideal :
      ((MaxContactCoverData.balancedTunedIdeal (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv).comap
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv)).comap
        (Limits.pullback.fst
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
      = ((MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrimv).comap
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)).comap
        (Limits.pullback.snd
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) :=
    i1.trans (i2.trans (i3.trans i4))
  have hE'' : removeUnitIdeals E' = removeUnitIdeals (List.map (fun D => D.comap h) T.boundary) :=
    (removeUnitIdeals_eq_of_sameNontrivialBoundary hE).symm
  have b1 :
      List.map (fun D => D.comap
          (Limits.pullback.fst
            (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
        (List.map (fun D => D.comap
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
          (removeUnitIdeals E'))
      = List.map (fun D => D.comap
          (Limits.pullback.fst
              (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
              (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
            MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
          (removeUnitIdeals E') := map_comap_map_comap _ _ _
  have hb :
      removeUnitIdeals (List.map (fun D => D.comap
          (Limits.pullback.fst
            (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
        (List.map (fun D => D.comap
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
          (removeUnitIdeals E')))
      = removeUnitIdeals (List.map (fun D => D.comap
          (Limits.pullback.snd
            (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
        (List.map (fun D => D.comap
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
          (MaxContactReduction.dropTrivialBoundary T).boundary)) :=
    calc removeUnitIdeals (List.map (fun D => D.comap
          (Limits.pullback.fst
            (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
        (List.map (fun D => D.comap
          (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
          (removeUnitIdeals E')))
        = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.fst
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
            (removeUnitIdeals E')) := congrArg removeUnitIdeals b1
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.fst
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
            E') := removeUnitIdeals_map_comap_removeUnitIdeals _ _
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.fst
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv))
            (List.map (fun D => D.comap h) T.boundary)) := removeUnitIdeals_map_comap_congr _ hE''
      _ = removeUnitIdeals (List.map (fun D => D.comap
            ((Limits.pullback.fst
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv) ≫ h))
            T.boundary) := congrArg removeUnitIdeals (map_comap_map_comap _ h _)
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.snd
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
            T.boundary) :=
          congrArg (fun φ => removeUnitIdeals (List.map (fun D => D.comap φ) T.boundary)) hcond2
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.snd
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
            (removeUnitIdeals T.boundary)) := (removeUnitIdeals_map_comap_removeUnitIdeals _ _).symm
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.snd
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
            (MaxContactReduction.dropTrivialBoundary T).boundary) :=
          congrArg (fun L => removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.snd
                (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
                (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
              MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) L))
            (dropTrivialBoundary_boundary_eq_removeUnitIdeals T).symm
      _ = removeUnitIdeals (List.map (fun D => D.comap
            (Limits.pullback.snd
              (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T (h ≫ T.structMap) h E') hpbv ≫ h)
              (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)))
          (List.map (fun D => D.comap
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
            (MaxContactReduction.dropTrivialBoundary T).boundary)) :=
          congrArg removeUnitIdeals (map_comap_map_comap _ _ _).symm
  exact markedIdealWithBoundary_mk_congr hsm hideal rfl hb

private theorem filter_eq_removeUnitIdeals {X : Scheme.{u}}
    (p : X.IdealSheafData → Bool) (hp : ∀ D : X.IdealSheafData, p D = true ↔ D ≠ ⊤)
    (L : List X.IdealSheafData) : L.filter p = removeUnitIdeals L := by
  induction L with
  | nil => rfl
  | cons D L ih =>
    by_cases hD : D = ⊤
    · subst hD
      have hpf : p (⊤ : X.IdealSheafData) = false := by
        cases hb : p (⊤ : X.IdealSheafData) with
        | false => rfl
        | true => exact absurd ((hp ⊤).1 hb) (fun hne => hne rfl)
      rw [removeUnitIdeals_cons_top]
      simp [hpf, ih]
    · have hpt : p D = true := (hp D).2 hD
      rw [removeUnitIdeals_cons_of_ne_top hD]
      simp [hpt, ih]

private theorem dropTrivialBoundary_eq_withBoundary_removeUnitIdeals (S : MarkedIdealWithBoundary.{u}) :
    MaxContactReduction.dropTrivialBoundary S = S.withBoundary (removeUnitIdeals S.boundary) := by
  rw [MaxContactReduction.dropTrivialBoundary_def]
  exact congrArg S.withBoundary
    (filter_eq_removeUnitIdeals _ (fun D => by simp) S.boundary)

private theorem ne_top_of_mem_removeUnitIdeals {X : Scheme.{u}} (L : List X.IdealSheafData) :
    ∀ D ∈ removeUnitIdeals L, D ≠ ⊤ := by
  induction L with
  | nil =>
    intro D hD
    simp [removeUnitIdeals] at hD
  | cons C L ih =>
    intro D hD
    by_cases hC : C = ⊤
    · subst hC
      rw [removeUnitIdeals_cons_top] at hD
      exact ih D hD
    · rw [removeUnitIdeals_cons_of_ne_top hC] at hD
      rcases List.mem_cons.1 hD with h1 | h1
      · subst h1; exact hC
      · exact ih D h1

private theorem isStrictPullback_coverMarkedSequence_of_eq_of_heq (hinv : ComapIsoInvariance.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) {S₁ S₂ : MarkedIdealWithBoundary.{u}} (hS : S₁ = S₂)
    (hv₁ : S₁.IsAdmissible) (hv₂ : S₂.IsAdmissible) (e₁ : BlowupSequenceData S₁.scheme) (e₂ : BlowupSequenceData S₂.scheme)
    (hee : HEq e₁ e₂)
    (hd : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap S₁ hv₁)
        (MaxContactCoverData.coverMarkedBlowupData S₁ hv₁ hinv (lowerDimensionalFamily A S₁)).toSequenceOfBlowups e₁.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap S₂ hv₂)
        (MaxContactCoverData.coverMarkedBlowupData S₂ hv₂ hinv (lowerDimensionalFamily A S₂)).toSequenceOfBlowups e₂.toSequenceOfBlowups := by
  subst hS
  cases hee
  exact hd

private theorem orderReductionHypotheses_of_eq {P : ℕ → Prop} {S₁ S₂ : MarkedIdealWithBoundary.{u}}
    (hS : S₁ = S₂) (hy : OrderReductionHypotheses P S₁) : OrderReductionHypotheses P S₂ := by
  subst hS
  exact hy

private theorem isPullback_of_faithfullyFlat_covers {X Y : Scheme.{u}} (h : Y ⟶ X)
    [AlgebraicGeometry.Flat h] {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ X) (c₂ : C₂ ⟶ Y)
    (hf₁ : AlgebraicGeometry.Flat c₁) (hs₁ : AlgebraicGeometry.Surjective c₁)
    (hf₂ : AlgebraicGeometry.Flat c₂) (hs₂ : AlgebraicGeometry.Surjective c₂)
    (t₁ : SequenceOfBlowups C₁) (t₂ : SequenceOfBlowups C₂) (s₁ : SequenceOfBlowups X) (s₂ : SequenceOfBlowups Y)
    (hd₁ : IsStrictPullbackBlowupSeq c₁ t₁ s₁) (hd₂ : IsStrictPullbackBlowupSeq c₂ t₂ s₂)
    (hne₂ : ∀ i, i < t₂.length → t₂.center i ≠ ⊤)
    (hcomp : ∀ v v' : SequenceOfBlowups (Limits.pullback (c₂ ≫ h) c₁),
      IsStrictPullbackBlowupSeq (Limits.pullback.fst (c₂ ≫ h) c₁) v t₂ →
      IsStrictPullbackBlowupSeq (Limits.pullback.snd (c₂ ≫ h) c₁) v' t₁ →
      v.withoutIsoBlowups.Isomorphic v'.withoutIsoBlowups) :
    IsPullbackBlowupSequence h s₂ s₁ := by
  have := hf₁
  have := hs₁
  have := hf₂
  have := hs₂
  have hfc : AlgebraicGeometry.Flat (c₂ ≫ h) :=
    CategoryTheory.MorphismProperty.comp_mem _ c₂ h inferInstance inferInstance
  have hflfst : AlgebraicGeometry.Flat (Limits.pullback.fst (c₂ ≫ h) c₁) := inferInstance
  have hsufst : AlgebraicGeometry.Surjective (Limits.pullback.fst (c₂ ≫ h) c₁) := inferInstance
  have hw : IsStrictPullbackBlowupSeq h (s₁.baseChange h) s₁ :=
    isStrictPullbackSequenceOfBlowups_baseChange s₁ h
  refine (IsStrictPullbackBlowupSeq.isPullbackSequenceOfBlowups_withoutIsoBlowups hw).of_isomorphic ?_
  have hu : IsStrictPullbackBlowupSeq (c₂ ≫ h) (s₁.baseChange (c₂ ≫ h)) s₁ :=
    isStrictPullbackSequenceOfBlowups_baseChange s₁ (c₂ ≫ h)
  have hu' : IsStrictPullbackBlowupSeq c₂ (s₁.baseChange (c₂ ≫ h)) (s₁.baseChange h) :=
    hu.baseChange_of_comp
  have hv : IsStrictPullbackBlowupSeq (Limits.pullback.fst (c₂ ≫ h) c₁)
      ((s₁.baseChange (c₂ ≫ h)).baseChange (Limits.pullback.fst (c₂ ≫ h) c₁))
      (s₁.baseChange (c₂ ≫ h)) := isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hv2 : IsStrictPullbackBlowupSeq (Limits.pullback.fst (c₂ ≫ h) c₁)
      (t₂.baseChange (Limits.pullback.fst (c₂ ≫ h) c₁)) t₂ :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hv1 : IsStrictPullbackBlowupSeq (Limits.pullback.snd (c₂ ≫ h) c₁)
      (t₁.baseChange (Limits.pullback.snd (c₂ ≫ h) c₁)) t₁ :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have e1 : IsStrictPullbackBlowupSeq (Limits.pullback.snd (c₂ ≫ h) c₁ ≫ c₁)
      ((s₁.baseChange (c₂ ≫ h)).baseChange (Limits.pullback.fst (c₂ ≫ h) c₁)) s₁ :=
    (hv.comp hu).congr_hom Limits.pullback.condition
  have e2 : IsStrictPullbackBlowupSeq (Limits.pullback.snd (c₂ ≫ h) c₁ ≫ c₁)
      (t₁.baseChange (Limits.pullback.snd (c₂ ≫ h) c₁)) s₁ := hv1.comp hd₁
  have e3 : ((s₁.baseChange (c₂ ≫ h)).baseChange
      (Limits.pullback.fst (c₂ ≫ h) c₁)).Isomorphic
      (t₁.baseChange (Limits.pullback.snd (c₂ ≫ h) c₁)) := e1.isomorphic e2
  have hmid : (s₁.baseChange (c₂ ≫ h)).withoutIsoBlowups.Isomorphic t₂.withoutIsoBlowups :=
    IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hv.withoutIsoBlowups hv2.withoutIsoBlowups
      ((e3.withoutIsoBlowups).trans (hcomp _ _ hv2 hv1).symm)
  have hfin : (s₁.baseChange h).withoutIsoBlowups.Isomorphic s₂.withoutIsoBlowups :=
    IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hu'.withoutIsoBlowups hd₂.withoutIsoBlowups hmid
  exact hfin.trans (SequenceOfBlowups.withoutIsoBlowups_isomorphic_self s₂
    (fun i hi => hd₂.center_ne_top_of_forall_center_ne_top hne₂ i hi))

private theorem smooth_pullback_fst_snd_and_surjective_fst {X Y : Scheme.{u}} (h : Y ⟶ X)
    [AlgebraicGeometry.Smooth h]
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ X) (c₂ : C₂ ⟶ Y)
    [AlgebraicGeometry.Smooth c₁] [AlgebraicGeometry.Smooth c₂]
    [AlgebraicGeometry.Surjective c₁] :
    AlgebraicGeometry.Smooth (Limits.pullback.fst (c₂ ≫ h) c₁) ∧
      AlgebraicGeometry.Smooth (Limits.pullback.snd (c₂ ≫ h) c₁) ∧
        AlgebraicGeometry.Surjective (Limits.pullback.fst (c₂ ≫ h) c₁) := by
  have hcc : AlgebraicGeometry.Smooth (c₂ ≫ h) := inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem smoothPullbackTriple_eq_dropTrivialBoundary (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}}
    (q : X' ⟶ S.scheme) :
    smoothPullbackTriple S q = MaxContactReduction.dropTrivialBoundary (S.pullbackAlong X' (q ≫ S.structMap) q) :=
  (dropTrivialBoundary_eq_withBoundary_removeUnitIdeals (S.pullbackAlong X' (q ≫ S.structMap) q)).symm

private theorem boundary_ne_top_of_eq {S₁ S₂ : MarkedIdealWithBoundary.{u}} (hS : S₁ = S₂)
    (hb : ∀ D ∈ S₁.boundary, D ≠ ⊤) : ∀ D ∈ S₂.boundary, D ≠ ⊤ := by
  subst hS
  exact hb

private theorem coverTriple_boundary_ne_top (S : MarkedIdealWithBoundary.{u}) (hv : S.IsAdmissible)
    [AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap S hv)]
    (hb : ∀ D ∈ S.boundary, D ≠ ⊤) :
    ∀ D ∈ (MaxContactCoverData.coverTriple S hv).boundary, D ≠ ⊤ := by
  refine boundary_ne_top_of_eq (MaxContactOpenCover.coverTriple_eq_tunedTriple_pullbackAlong S hv).symm ?_
  intro D hD
  have hD2 : D ∈ List.map (fun D₀ : S.scheme.IdealSheafData =>
      D₀.comap (MaxContactCoverData.coverMap S hv)) S.boundary := hD
  obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD2
  exact (comap_ne_top_iff_of_surjective (MaxContactCoverData.coverMap S hv) D₀).2 (hb D₀ hD₀)

private theorem orderAt_coverTriple_le_mult (hstar0 : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
    (horder : CoSupportTunedSheafEqAndOrderLE.{u}) (S : MarkedIdealWithBoundary.{u}) (hv : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hmax : MaxOrderEq S.ideal S.mult) :
    ∀ x : ↥(MaxContactCoverData.coverTriple S hv).scheme,
      orderAt (MaxContactCoverData.coverTriple S hv).ideal x
        ≤ ((MaxContactCoverData.coverTriple S hv).mult : ℕ∞) := by
  have hgood := MaxContactCoverData.isMaxContactCover_chosenCoverData S hv (hstar0.exists_goodCover S hv hord)
  have hcv : (MaxContactCoverData.coverTriple S hv).IsAdmissible :=
    hstar0.coverTriple_valid S hv hord hgood
  have hsm : AlgebraicGeometry.Smooth S.structMap := hv.smooth
  have hft : AlgebraicGeometry.LocallyOfFiniteType S.structMap := hv.locallyOfFiniteType
  have hcz : CharZero S.base := hv.charZero
  have hnoe : IsNoetherianRing S.base := inferInstance
  have hsmc : AlgebraicGeometry.Smooth (MaxContactCoverData.coverMap S hv) :=
    MaxContactCoverData.smooth_coverMap_of_isAdmissible S hv
  have hs : 1 ≤ MaxContactCoverData.tunedMult S := hcv.one_le_mult
  have hOL : OrderLE (MaxContactCoverData.balancedTunedIdeal S hv) (MaxContactCoverData.tunedMult S) :=
    horder.orderLE S.base S.scheme S.structMap S.ideal S.mult hv.one_le_mult hmax
      (MaxContactCoverData.tunedMult S) hs
  have hOL' : ∀ y : ↥S.scheme, orderAt (MaxContactCoverData.balancedTunedIdeal S hv) y
      ≤ ((MaxContactCoverData.tunedMult S : ℕ) : ℕ∞) := hOL
  intro x
  show orderAt ((MaxContactCoverData.balancedTunedIdeal S hv).comap (MaxContactCoverData.coverMap S hv)) x
      ≤ ((MaxContactCoverData.tunedMult S : ℕ) : ℕ∞)
  rw [orderAt_comap S.base S.structMap (MaxContactCoverData.coverMap S hv)
    (MaxContactCoverData.balancedTunedIdeal S hv) x]
  exact hOL' _

private theorem withoutIsoBlowups_isomorphic_of_smoothPullbackTriple_eq
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (hshift : IsBoundaryPositionInvariant P A)
    (hstar0 : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u})
    (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (hdel : LoopCompatibleWithSmoothPullback hinv P A) (htv : DropTrivialBoundaryAdmissible.{u})
    (S₁ S₂ : MarkedIdealWithBoundary.{u}) (hv₁ : S₁.IsAdmissible) (hv₂ : S₂.IsAdmissible)
    (hP₁ : P S₁.krullDimSucc) (hP₂ : P S₂.krullDimSucc)
    (hord₁ : ∀ x : ↥S₁.scheme, orderAt S₁.ideal x ≤ (S₁.mult : ℕ∞))
    (hord₂ : ∀ x : ↥S₂.scheme, orderAt S₂.ideal x ≤ (S₂.mult : ℕ∞))
    (_hcsn₁ : (orderAtLeastLocus S₁.ideal S₁.mult).Nonempty)
    (_hcsn₂ : (orderAtLeastLocus S₂.ideal S₂.mult).Nonempty)
    (hbd₁ : ∀ D ∈ S₁.boundary, D ≠ ⊤) (hbd₂ : ∀ D ∈ S₂.boundary, D ≠ ⊤)
    (hsuc₁ : AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap S₁ hv₁))
    (hsuc₂ : AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap S₂ hv₂))
    (hcord₁ : ∀ x : ↥(MaxContactCoverData.coverTriple S₁ hv₁).scheme,
      orderAt (MaxContactCoverData.coverTriple S₁ hv₁).ideal x
        ≤ ((MaxContactCoverData.coverTriple S₁ hv₁).mult : ℕ∞))
    (hcord₂ : ∀ x : ↥(MaxContactCoverData.coverTriple S₂ hv₂).scheme,
      orderAt (MaxContactCoverData.coverTriple S₂ hv₂).ideal x
        ≤ ((MaxContactCoverData.coverTriple S₂ hv₂).mult : ℕ∞))
    {Q : Scheme.{u}}
    (π₁ : Q ⟶ (MaxContactCoverData.coverTriple S₁ hv₁).scheme)
    (π₂ : Q ⟶ (MaxContactCoverData.coverTriple S₂ hv₂).scheme)
    (hsmπ₁ : AlgebraicGeometry.Smooth π₁) (hsmπ₂ : AlgebraicGeometry.Smooth π₂)
    (hdeleq : smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂
      = smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁)
    (hqc : AlgebraicGeometry.QuasiCompact
      (π₁ ≫ (MaxContactCoverData.coverTriple S₁ hv₁).structMap))
    (hdim : (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).krullDimSucc ≤ S₂.krullDimSucc)
    (v v' : SequenceOfBlowups Q)
    (hvv : IsStrictPullbackBlowupSeq π₂ v
      (MaxContactCoverData.coverMarkedBlowupData S₂ hv₂ hinv (lowerDimensionalFamily A S₂)).toSequenceOfBlowups)
    (hvv' : IsStrictPullbackBlowupSeq π₁ v'
      (MaxContactCoverData.coverMarkedBlowupData S₁ hv₁ hinv (lowerDimensionalFamily A S₁)).toSequenceOfBlowups) :
    v.withoutIsoBlowups.Isomorphic v'.withoutIsoBlowups := by
  have := hqc
  have := hsuc₁
  have := hsuc₂
  have := hsmπ₁
  have := hsmπ₂
  have hgood₁ := MaxContactCoverData.isMaxContactCover_chosenCoverData S₁ hv₁ (hstar0.exists_goodCover S₁ hv₁ hord₁)
  have hgood₂ := MaxContactCoverData.isMaxContactCover_chosenCoverData S₂ hv₂ (hstar0.exists_goodCover S₂ hv₂ hord₂)
  have hcv₁ : (MaxContactCoverData.coverTriple S₁ hv₁).IsAdmissible :=
    hstar0.coverTriple_valid S₁ hv₁ hord₁ hgood₁
  have hcv₂ : (MaxContactCoverData.coverTriple S₂ hv₂).IsAdmissible :=
    hstar0.coverTriple_valid S₂ hv₂ hord₂ hgood₂
  have : AlgebraicGeometry.Smooth (MaxContactCoverData.coverTriple S₁ hv₁).structMap := hcv₁.smooth
  have : AlgebraicGeometry.Smooth (MaxContactCoverData.coverTriple S₂ hv₂).structMap := hcv₂.smooth
  have : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.coverTriple S₁ hv₁).structMap := hcv₁.locallyOfFiniteType
  have : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.coverTriple S₂ hv₂).structMap := hcv₂.locallyOfFiniteType
  have : CharZero (MaxContactCoverData.coverTriple S₁ hv₁).base := hcv₁.charZero
  have : CharZero (MaxContactCoverData.coverTriple S₂ hv₂).base := hcv₂.charZero
  have hm₁ : 1 ≤ (MaxContactCoverData.coverTriple S₁ hv₁).mult := hcv₁.one_le_mult
  have hm₂ : 1 ≤ (MaxContactCoverData.coverTriple S₂ hv₂).mult := hcv₂.one_le_mult
  have hcdim₁ : (MaxContactCoverData.coverTriple S₁ hv₁).krullDimSucc ≤ S₁.krullDimSucc :=
    hstar0.coverTriple_dim_le S₁ hv₁
  have hcdim₂ : (MaxContactCoverData.coverTriple S₂ hv₂).krullDimSucc ≤ S₂.krullDimSucc :=
    hstar0.coverTriple_dim_le S₂ hv₂
  have hcadm₁ : ∀ [inst : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.coverTriple S₁ hv₁).structMap],
      IsMaxContactHypersurface (MaxContactCoverData.coverTriple S₁ hv₁).base
        (MaxContactCoverData.coverTriple S₁ hv₁).structMap
        (MaxContactCoverData.coverTriple S₁ hv₁).ideal
        (MaxContactCoverData.coverTriple S₁ hv₁).mult
        (MaxContactCoverData.coverMaxContactIdeal S₁ hv₁) := by
    intro _inst
    exact hstar0.coverContact_admissible S₁ hv₁ hgood₁
  have hcadm₂ : ∀ [inst : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.coverTriple S₂ hv₂).structMap],
      IsMaxContactHypersurface (MaxContactCoverData.coverTriple S₂ hv₂).base
        (MaxContactCoverData.coverTriple S₂ hv₂).structMap
        (MaxContactCoverData.coverTriple S₂ hv₂).ideal
        (MaxContactCoverData.coverTriple S₂ hv₂).mult
        (MaxContactCoverData.coverMaxContactIdeal S₂ hv₂) := by
    intro _inst
    exact hstar0.coverContact_admissible S₂ hv₂ hgood₂
  have hcsnc₁ : InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple S₁ hv₁).structMap
      [MaxContactCoverData.coverMaxContactIdeal S₁ hv₁] := hstar0.coverContact_snc S₁ hv₁ hgood₁
  have hcsnc₂ : InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple S₂ hv₂).structMap
      [MaxContactCoverData.coverMaxContactIdeal S₂ hv₂] := hstar0.coverContact_snc S₂ hv₂ hgood₂
  have hcbd₁ : ∀ D ∈ (MaxContactCoverData.coverTriple S₁ hv₁).boundary, D ≠ ⊤ :=
    coverTriple_boundary_ne_top S₁ hv₁ hbd₁
  have hcbd₂ : ∀ D ∈ (MaxContactCoverData.coverTriple S₂ hv₂).boundary, D ≠ ⊤ :=
    coverTriple_boundary_ne_top S₂ hv₂ hbd₂
  have hpbv₁ : ((MaxContactCoverData.coverTriple S₁ hv₁).pullbackAlong Q
      (π₁ ≫ (MaxContactCoverData.coverTriple S₁ hv₁).structMap) π₁).IsAdmissible :=
    hin.valid_pullbackAlong (MaxContactCoverData.coverTriple S₁ hv₁) hcv₁ Q
      (π₁ ≫ (MaxContactCoverData.coverTriple S₁ hv₁).structMap) π₁ rfl
  have hdv₁ : (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).IsAdmissible := by
    rw [smoothPullbackTriple_eq_dropTrivialBoundary]
    exact htv _ hpbv₁
  have hdv₂ : (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).IsAdmissible := by
    rw [hdeleq]
    exact hdv₁
  have hdim₂ : (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).krullDimSucc ≤ S₂.krullDimSucc := by
    rw [hdeleq]
    exact hdim
  have hdord₁ : ∀ x : ↥(smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).scheme,
      orderAt (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).ideal x
        ≤ ((smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).mult : ℕ∞) :=
    fun x => BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult (MaxContactCoverData.coverTriple S₁ hv₁) π₁ hcv₁ hcord₁ x
  have hdadm₁ : ∀ [inst : AlgebraicGeometry.LocallyOfFiniteType
      (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap],
      IsMaxContactHypersurface (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).base
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).ideal
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).mult
        ((MaxContactCoverData.coverMaxContactIdeal S₁ hv₁).comap π₁) := by
    intro inst
    have : AlgebraicGeometry.LocallyOfFiniteType
        (π₁ ≫ (MaxContactCoverData.coverTriple S₁ hv₁).structMap) := inst
    exact hAdm (MaxContactCoverData.coverTriple S₁ hv₁).base
      (MaxContactCoverData.coverTriple S₁ hv₁).scheme (MaxContactCoverData.coverTriple S₁ hv₁).structMap
      Q π₁ (MaxContactCoverData.coverTriple S₁ hv₁).ideal (MaxContactCoverData.coverTriple S₁ hv₁).mult
      hm₁ (MaxContactCoverData.coverMaxContactIdeal S₁ hv₁) hcadm₁
  have hdadm₂ : ∀ [inst : AlgebraicGeometry.LocallyOfFiniteType
      (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).structMap],
      IsMaxContactHypersurface (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).base
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).structMap
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).ideal
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).mult
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂) := by
    intro inst
    have : AlgebraicGeometry.LocallyOfFiniteType
        (π₂ ≫ (MaxContactCoverData.coverTriple S₂ hv₂).structMap) := inst
    exact hAdm (MaxContactCoverData.coverTriple S₂ hv₂).base
      (MaxContactCoverData.coverTriple S₂ hv₂).scheme (MaxContactCoverData.coverTriple S₂ hv₂).structMap
      Q π₂ (MaxContactCoverData.coverTriple S₂ hv₂).ideal (MaxContactCoverData.coverTriple S₂ hv₂).mult
      hm₂ (MaxContactCoverData.coverMaxContactIdeal S₂ hv₂) hcadm₂
  have hdsnc₁ : InStrictNormalCrossingPosition (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap
      [(MaxContactCoverData.coverMaxContactIdeal S₁ hv₁).comap π₁] :=
    inStrictNormalCrossingPosition_comap_singleton (MaxContactCoverData.coverTriple S₁ hv₁).structMap π₁
      (MaxContactCoverData.coverMaxContactIdeal S₁ hv₁) hcsnc₁
  have hdsnc₂ : InStrictNormalCrossingPosition (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).structMap
      [(MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂] :=
    inStrictNormalCrossingPosition_comap_singleton (MaxContactCoverData.coverTriple S₂ hv₂).structMap π₂
      (MaxContactCoverData.coverMaxContactIdeal S₂ hv₂) hcsnc₂
  have hA : IsPullbackBlowupSequence π₁
      (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁)
        ((MaxContactCoverData.coverMaxContactIdeal S₁ hv₁).comap π₁)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactCoverData.coverMarkedBlowupData S₁ hv₁ hinv (lowerDimensionalFamily A S₁)).toSequenceOfBlowups :=
    hdel hstar0 hin hMC hAdm hmono B hspec hshift S₁ S₂ hP₁ hP₂
      (MaxContactCoverData.coverTriple S₁ hv₁) hcv₁ hcord₁ hcdim₁
      (MaxContactCoverData.coverMaxContactIdeal S₁ hv₁) hcadm₁ hcsnc₁ hcbd₁ π₁ hdv₁ hdim hdadm₁ hdsnc₁
  have hB : IsPullbackBlowupSequence π₂
      (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂)
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactCoverData.coverMarkedBlowupData S₂ hv₂ hinv (lowerDimensionalFamily A S₂)).toSequenceOfBlowups :=
    hdel hstar0 hin hMC hAdm hmono B hspec hshift S₂ S₂ hP₂ hP₂
      (MaxContactCoverData.coverTriple S₂ hv₂) hcv₂ hcord₂ hcdim₂
      (MaxContactCoverData.coverMaxContactIdeal S₂ hv₂) hcadm₂ hcsnc₂ hcbd₂ π₂ hdv₂ hdim₂ hdadm₂ hdsnc₂
  have hu : (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂)
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      = (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁)
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    eq_of_heq (reduceAlongHypersurface_toSequenceOfBlowups_heq hinv S₂ (lowerDimensionalFamily A S₂) hdeleq
      ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)
      ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂) HEq.rfl)
  have hdsnc₂' : InStrictNormalCrossingPosition (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap
      [(MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂] :=
    inStrictNormalCrossingPosition_of_triple_eq hdeleq.symm
      [(MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂]
      [(MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂] HEq.rfl hdsnc₂
  have hdadm₂' : ∀ [inst : AlgebraicGeometry.LocallyOfFiniteType
      (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap],
      IsMaxContactHypersurface (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).base
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).structMap
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).ideal
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁).mult
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂) := by
    intro inst
    have hft2 : AlgebraicGeometry.LocallyOfFiniteType
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₂ hv₂) π₂).structMap := by
      rw [hdeleq]
      exact inst
    exact isMaxContactHypersurface_of_triple_eq hdeleq.symm inst hft2
      ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)
      ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂) HEq.rfl (@hdadm₂ hft2)
  have hmid : (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁)
        ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)).toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic
      (MaxContactReduction.reduceAlongHypersurface hinv S₂ (lowerDimensionalFamily A S₂)
        (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁)
        ((MaxContactCoverData.coverMaxContactIdeal S₁ hv₁).comap π₁)).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    reduceAlongHypersurface_isomorphic_of_isMaxContactHypersurface hinv P hmono A B hspec hshift hstar0
      hin hMC hAdm
      S₂ hP₂ (smoothPullbackTriple (MaxContactCoverData.coverTriple S₁ hv₁) π₁) hdv₁ hdord₁ hdim
      ((MaxContactCoverData.coverMaxContactIdeal S₂ hv₂).comap π₂)
      ((MaxContactCoverData.coverMaxContactIdeal S₁ hv₁).comap π₁)
      hdadm₂' hdsnc₂' hdadm₁ hdsnc₁
  have e₂ := IsPullbackBlowupSequence.isomorphic hvv.isPullbackSequenceOfBlowups_withoutIsoBlowups hB
  have e₁ := IsPullbackBlowupSequence.isomorphic hvv'.isPullbackSequenceOfBlowups_withoutIsoBlowups hA
  rw [hu] at e₂
  exact e₂.trans (hmid.trans e₁.symm)

theorem maxContactPrincipalization_isPullbackBlowupSequence_of_smooth
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (hshift : IsBoundaryPositionInvariant P A)
    (hstar0 : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u})
    (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (hdel : LoopCompatibleWithSmoothPullback hinv P A) (hvan : TrivialOnEmptyOrderLocus hinv P A)
    (hsf : CoverSequenceProperties hinv P A) (hmd : MarkingDescends hinv P A)
    (hff : CoverFaithfullyFlat.{u} P) (htv : DropTrivialBoundaryAdmissible.{u}) (htm : MarkedOfMarkedDropTrivialBoundary.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hP : P T.krullDimSucc)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Flat h]
    (hq : h ≫ T.structMap = qY)
    (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y qY h).boundary E')
    (hv' : ((T.pullbackAlong Y qY h).withBoundary E').IsAdmissible)
    (hP' : P ((T.pullbackAlong Y qY h).withBoundary E').krullDimSucc)
    (htrimv : (MaxContactReduction.dropTrivialBoundary T).IsAdmissible)
    (hpbv : (dropTrivialBoundaryPullback T qY h E').IsAdmissible)
    (hqc : AlgebraicGeometry.QuasiCompact
      (Limits.pullback.snd (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) ≫
        (MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) htrimv).structMap))
    (hdimfp : krullDimSucc
        (Limits.pullback (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)) ≤
      (T.pullbackAlong Y qY h).krullDimSucc) :
    IsPullbackBlowupSequence h
      (maxContactPrincipalization hinv A ((T.pullbackAlong Y qY h).withBoundary E')).toSequenceOfBlowups
      (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have horder : CoSupportTunedSheafEqAndOrderLE.{u} :=
    hstar0.tuning.coSupport_tunedSheaf_eq_and_orderLE
  have hord₂ : ∀ x : ↥((T.pullbackAlong Y qY h).withBoundary E').scheme,
      orderAt ((T.pullbackAlong Y qY h).withBoundary E').ideal x
        ≤ ((((T.pullbackAlong Y qY h).withBoundary E').mult : ℕ) : ℕ∞) :=
    fun x => BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult T h hv hord x
  by_cases hemp₂ : orderAtLeastLocus (T.ideal.comap h) T.mult = (∅ : Set ↥Y)
  · have hlen₂ :
        (maxContactPrincipalization hinv A ((T.pullbackAlong Y qY h).withBoundary E')).toSequenceOfBlowups.length = 0 :=
      length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A _ hv' hP' hord₂ hemp₂
    by_cases hemp₁ : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
    · exact isPullback_of_length_eq_zero_of_length_eq_zero h _ _ hlen₂
        (length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hP hord hemp₁)
    · exact hvan T ⟨hP, hord, Set.nonempty_iff_ne_empty.mpr hemp₁, hv⟩ h _ hlen₂ hemp₂
  · have hcs₂ : (orderAtLeastLocus (T.ideal.comap h) T.mult).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hemp₂
    have hcs₁ : (orderAtLeastLocus T.ideal T.mult).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hzero
      exact hemp₂ (orderAtLeastLocus_comap_eq_empty T hv h hzero)
    have hypT : OrderReductionHypotheses P T := ⟨hP, hord, hcs₁, hv⟩
    have hypT₂ : OrderReductionHypotheses P ((T.pullbackAlong Y qY h).withBoundary E') := ⟨hP', hord₂, hcs₂, hv'⟩
    obtain ⟨d₁, hd₁, he₁⟩ := exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm T hypT
    obtain ⟨d₂, hd₂, he₂⟩ := exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm
      ((T.pullbackAlong Y qY h).withBoundary E') hypT₂
    have htrim₂ : MaxContactReduction.dropTrivialBoundary ((T.pullbackAlong Y qY h).withBoundary E')
        = dropTrivialBoundaryPullback T qY h E' :=
      (dropTrivialBoundary_eq_withBoundary_removeUnitIdeals ((T.pullbackAlong Y qY h).withBoundary E')).trans rfl
    have hypS₁ : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := hypT.of_dropTrivialBoundaryAdmissible htv
    have hypS₂ : OrderReductionHypotheses P (dropTrivialBoundaryPullback T qY h E') :=
      orderReductionHypotheses_of_eq htrim₂ (hypT₂.of_dropTrivialBoundaryAdmissible htv)
    have hd₁' : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)
        (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrimv hinv
          (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toSequenceOfBlowups d₁.toSequenceOfBlowups := hd₁
    have hd₂' : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv)
        (MaxContactCoverData.coverMarkedBlowupData (dropTrivialBoundaryPullback T qY h E') hpbv hinv
          (lowerDimensionalFamily A (dropTrivialBoundaryPullback T qY h E'))).toSequenceOfBlowups d₂.toSequenceOfBlowups :=
      isStrictPullback_coverMarkedSequence_of_eq_of_heq hinv A htrim₂ ((hypT₂.of_dropTrivialBoundaryAdmissible htv).valid) hpbv d₂ d₂
        HEq.rfl hd₂
    have hfl₁ : AlgebraicGeometry.Flat
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) :=
      (hff (MaxContactReduction.dropTrivialBoundary T) hypS₁).2
    have hsu₁ : AlgebraicGeometry.Surjective
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) :=
      (hff (MaxContactReduction.dropTrivialBoundary T) hypS₁).1
    have hfl₂ : AlgebraicGeometry.Flat
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv) :=
      (hff (dropTrivialBoundaryPullback T qY h E') hypS₂).2
    have hsu₂ : AlgebraicGeometry.Surjective
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv) :=
      (hff (dropTrivialBoundaryPullback T qY h E') hypS₂).1
    have hne₂ : ∀ i, i < (MaxContactCoverData.coverMarkedBlowupData (dropTrivialBoundaryPullback T qY h E') hpbv hinv
          (lowerDimensionalFamily A (dropTrivialBoundaryPullback T qY h E'))).toSequenceOfBlowups.length →
        (MaxContactCoverData.coverMarkedBlowupData (dropTrivialBoundaryPullback T qY h E') hpbv hinv
          (lowerDimensionalFamily A (dropTrivialBoundaryPullback T qY h E'))).toSequenceOfBlowups.center i ≠ ⊤ :=
      fun i hi => hsf.center_ne_top (dropTrivialBoundaryPullback T qY h E') hypS₂ i hi
    have hsmc₁ : AlgebraicGeometry.Smooth
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv) :=
      MaxContactCoverData.smooth_coverMap_of_isAdmissible _ htrimv
    have hsmc₂ : AlgebraicGeometry.Smooth
        (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv) :=
      MaxContactCoverData.smooth_coverMap_of_isAdmissible _ hpbv
    have hpbf := @smooth_pullback_fst_snd_and_surjective_fst T.scheme Y h ‹AlgebraicGeometry.Smooth h› _ _
      (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)
      (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv)
      hsmc₁ hsmc₂ hsu₁
    have hbdT : ∀ D ∈ (MaxContactReduction.dropTrivialBoundary T).boundary, D ≠ ⊤ :=
      boundary_ne_top_of_eq (dropTrivialBoundary_eq_withBoundary_removeUnitIdeals T).symm
        (fun D hD => ne_top_of_mem_removeUnitIdeals T.boundary D hD)
    have hbdP : ∀ D ∈ (dropTrivialBoundaryPullback T qY h E').boundary, D ≠ ⊤ :=
      fun D hD => ne_top_of_mem_removeUnitIdeals E' D hD
    have hmax₁ : MaxOrderEq (MaxContactReduction.dropTrivialBoundary T).ideal (MaxContactReduction.dropTrivialBoundary T).mult :=
      ⟨hypS₁.orderLE, hypS₁.coSupport_nonempty⟩
    have hmax₂ : MaxOrderEq (dropTrivialBoundaryPullback T qY h E').ideal
        (dropTrivialBoundaryPullback T qY h E').mult :=
      ⟨hypS₂.orderLE, hypS₂.coSupport_nonempty⟩
    have hcord₁ := orderAt_coverTriple_le_mult hstar0 horder (MaxContactReduction.dropTrivialBoundary T) htrimv hord hmax₁
    have hcord₂ := orderAt_coverTriple_le_mult hstar0 horder (dropTrivialBoundaryPullback T qY h E') hpbv
      hord₂ hmax₂
    have hdeleq := @smoothPullbackTriple_coverTriple_eq T Y qY h ‹AlgebraicGeometry.Smooth h› hq E' hE
      htrimv hpbv hsu₂ hpbf.2.2
    rw [he₁, he₂]
    refine isPullback_of_faithfullyFlat_covers h
      (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv)
      (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv)
      hfl₁ hsu₁ hfl₂ hsu₂
      (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrimv hinv
        (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toSequenceOfBlowups
      (MaxContactCoverData.coverMarkedBlowupData (dropTrivialBoundaryPullback T qY h E') hpbv hinv
        (lowerDimensionalFamily A (dropTrivialBoundaryPullback T qY h E'))).toSequenceOfBlowups
      d₁.toSequenceOfBlowups d₂.toSequenceOfBlowups hd₁' hd₂' hne₂ ?_
    intro v v' hvv hvv'
    exact withoutIsoBlowups_isomorphic_of_smoothPullbackTriple_eq hinv P hmono A B hspec hshift hstar0 hin hMC hAdm hdel htv
      (MaxContactReduction.dropTrivialBoundary T) (dropTrivialBoundaryPullback T qY h E') htrimv hpbv hP hP'
      hord hord₂ hypS₁.coSupport_nonempty hypS₂.coSupport_nonempty hbdT hbdP
      hsu₁ hsu₂ hcord₁ hcord₂
      (Limits.pullback.snd (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
      (Limits.pullback.fst (MaxContactCoverData.coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
        (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) htrimv))
      hpbf.2.1 hpbf.1 hdeleq hqc hdimfp v v' hvv hvv'

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution

end
