import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceDescentDatum
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMapSurjective
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusAfterReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactCoverDescent

private theorem morphismProperty_pullback_fst_self {X Y : Scheme.{u}} (g : Y ⟶ X) (Q : MorphismProperty Scheme.{u})
    (hQ : Q.IsStableUnderBaseChange) (hg : Q g) : Q (pullback.fst g g) :=
  hQ.of_isPullback (IsPullback.of_hasPullback g g).flip hg

private theorem morphismProperty_pullback_snd_self {X Y : Scheme.{u}} (g : Y ⟶ X) (Q : MorphismProperty Scheme.{u})
    (hQ : Q.IsStableUnderBaseChange) (hg : Q g) : Q (pullback.snd g g) :=
  hQ.of_isPullback (IsPullback.of_hasPullback g g) hg

private theorem morphismProperty_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Z)
    (Q : MorphismProperty Scheme.{u}) (hQ : Q.IsStableUnderComposition) (hf : Q f) (hp : Q p) :
    Q (f ≫ p) :=
  hQ.comp_mem f p hf hp

private theorem map_comap_map_comap_eq_of_comp_eq {W X Y : Scheme.{u}} (a b : W ⟶ X) (g : X ⟶ Y)
    (hab : a ≫ g = b ≫ g) (L : List Y.IdealSheafData) :
    List.map (fun D : X.IdealSheafData => D.comap a)
        (List.map (fun D : Y.IdealSheafData => D.comap g) L)
      = List.map (fun D : X.IdealSheafData => D.comap b)
        (List.map (fun D : Y.IdealSheafData => D.comap g) L) := by
  induction L with
  | nil => simp
  | cons D L ih =>
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih⟩
      have hD : D.comap (a ≫ g) = D.comap (b ≫ g) := by rw [hab]
      simpa using hD

private theorem heq_reduceAlongHypersurface_of_eq (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups)
    {S₁ S₂ : MarkedIdealWithBoundary.{u}} (hS : S₁ = S₂)
    (H₁ : S₁.scheme.IdealSheafData) (H₂ : S₂.scheme.IdealSheafData) (hH : HEq H₁ H₂) :
    HEq (MaxContactReduction.reduceAlongHypersurface hinv T resolveLower S₁ H₁).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T resolveLower S₂ H₂).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  subst hS
  have hEq : H₁ = H₂ := eq_of_heq hH
  subst hEq
  rfl

private theorem inStrictNormalCrossingPosition_comap_boundary (hin : OrderReduction.OrderReductionHypotheses.{u})
    (S' : MarkedIdealWithBoundary.{u})
    (hV : S'.IsAdmissible) {Y : Scheme.{u}} (f : Y ⟶ S'.scheme)
    (hf : AlgebraicGeometry.Smooth f)
    (hq : AlgebraicGeometry.QuasiCompact (f ≫ S'.structMap)) :
    InStrictNormalCrossingPosition (f ≫ S'.structMap)
      (List.map (fun D : S'.scheme.IdealSheafData => D.comap f) S'.boundary) := by
  have := hf
  have := hq
  have hpb := hin.valid_pullbackAlong S' hV Y (f ≫ S'.structMap) f rfl
  have hs : (S'.pullbackAlong Y (f ≫ S'.structMap) f).structMap = f ≫ S'.structMap :=
    MarkedIdealWithBoundary.pullbackAlong_structureMorphism S' Y (f ≫ S'.structMap) f
  have hb : (S'.pullbackAlong Y (f ≫ S'.structMap) f).boundary
      = List.map (fun D : S'.scheme.IdealSheafData => D.comap f) S'.boundary :=
    MarkedIdealWithBoundary.pullbackAlong_boundary S' Y (f ≫ S'.structMap) f
  have hsnc := hpb.snc
  rw [hs, hb] at hsnc
  exact hsnc

private theorem isStrictPullbackBlowupSeq_reduceAlongHypersurface_pullback (hstar : MaxContactCoverProperties.{u})
    (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hmc : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u}) (hsap : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hSV : S.IsAdmissible)
    (hSO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hSdim : S.krullDimSucc ≤ T.krullDimSucc) (H : S.scheme.IdealSheafData)
    (hH : ∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
    (hqsmooth : AlgebraicGeometry.Smooth q) (hqflat : AlgebraicGeometry.Flat q)
    (hqSu : AlgebraicGeometry.Surjective q) (hqEt : AlgebraicGeometry.Etale q)
    [AlgebraicGeometry.QuasiCompact (q ≫ S.structMap)]
    [AlgebraicGeometry.LocallyOfFiniteType (q ≫ S.structMap)]
    (H' : X'.IdealSheafData)
    (hadm' : IsMaxContactHypersurface S.base (q ≫ S.structMap) (S.ideal.comap q) S.mult H')
    (hsnc' : InStrictNormalCrossingPosition (q ≫ S.structMap) [H']) :
    IsStrictPullbackBlowupSeq q
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
        (LowerDimReductionPullback.pullbackTriple S q) H').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have := hqsmooth
  have := hqflat
  have := hqSu
  have := hqEt
  have hNS : AlgebraicGeometry.IsNoetherian S.scheme := hSV.isNoetherian
  have hLNS : AlgebraicGeometry.IsLocallyNoetherian S.scheme := inferInstance
  have hV' : (LowerDimReductionPullback.pullbackTriple S q).IsAdmissible :=
    hin.valid_pullbackAlong S hSV X' (q ≫ S.structMap) q rfl
  have hdim' : (LowerDimReductionPullback.pullbackTriple S q).krullDimSucc ≤ T.krullDimSucc :=
    le_trans (hin.schemeDim_le_of_etale X' S.scheme q hSV.topologicalKrullDim_lt_top) hSdim
  refine BoundarySeparationBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar hin hmc hsap hinv P hmono A B hspec T hPdimT
    S hSV hSO hSdim H hH hHsnc q hV' hdim' H' ?_ ?_
  · intro _inst
    exact hadm'
  · exact hsnc'

private theorem exists_isStrictPullbackBlowupSeq_reduceAlongHypersurface (hstar : MaxContactCoverProperties.{u})
    (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hmc : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u}) (hsap : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hSV : S.IsAdmissible)
    (hSO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hSdim : S.krullDimSucc ≤ T.krullDimSucc)
    (g : S.scheme ⟶ T.scheme)
    (hgEt : AlgebraicGeometry.Etale g) (hgsmooth : AlgebraicGeometry.Smooth g)
    (hgflat : AlgebraicGeometry.Flat g) (hgSu : AlgebraicGeometry.Surjective g)
    (φ : T.scheme ⟶ Spec (CommRingCat.of S.base)) (hgs : S.structMap = g ≫ φ)
    (J : T.scheme.IdealSheafData) (hgi : S.ideal = J.comap g)
    (E : List T.scheme.IdealSheafData)
    (hgb : S.boundary = List.map (fun D : T.scheme.IdealSheafData => D.comap g) E)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H]) :
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq g
        (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups
        d.toSequenceOfBlowups := by
  classical
  have := hSV.charZero
  have := hSV.smooth
  have := hSV.locallyOfFiniteType
  have := hSV.quasiCompact
  have := hgEt
  have := hgsmooth
  have := hgflat
  have := hgSu
  have hNS : AlgebraicGeometry.IsNoetherian S.scheme := hSV.isNoetherian
  have hNSp : TopologicalSpace.NoetherianSpace ↥S.scheme := inferInstance
  have hQCg : AlgebraicGeometry.QuasiCompact g :=
    ⟨fun U _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hcolS : ∀ (W : Scheme.{u}) (a b : W ⟶ S.scheme), a ≫ g = b ≫ g →
      a ≫ S.structMap = b ≫ S.structMap := by
    intro W a b hab
    rw [hgs, ← Category.assoc, ← Category.assoc, hab]
  have hcolI : ∀ (W : Scheme.{u}) (a b : W ⟶ S.scheme), a ≫ g = b ≫ g →
      S.ideal.comap a = S.ideal.comap b := by
    intro W a b hab
    have hD : J.comap (a ≫ g) = J.comap (b ≫ g) := by rw [hab]
    rw [hgi]
    simpa using hD
  have hcolB : ∀ (W : Scheme.{u}) (a b : W ⟶ S.scheme), a ≫ g = b ≫ g →
      List.map (fun D : S.scheme.IdealSheafData => D.comap a) S.boundary
        = List.map (fun D : S.scheme.IdealSheafData => D.comap b) S.boundary := by
    intro W a b hab
    rw [hgb]
    exact map_comap_map_comap_eq_of_comp_eq a b g hab E
  have hcol : ∀ (W : Scheme.{u}) (a b : W ⟶ S.scheme), a ≫ g = b ≫ g →
      LowerDimReductionPullback.pullbackTriple S a = LowerDimReductionPullback.pullbackTriple S b := by
    intro W a b hab
    simp only [LowerDimReductionPullback.pullbackTriple, MarkedIdealWithBoundary.pullbackAlong]
    rw [hcolS W a b hab, hcolI W a b hab, hcolB W a b hab]
  have hEt1 : AlgebraicGeometry.Etale (pullback.fst g g) :=
    morphismProperty_pullback_fst_self g (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hEt2 : AlgebraicGeometry.Etale (pullback.snd g g) :=
    morphismProperty_pullback_snd_self g (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hSm1 : AlgebraicGeometry.Smooth (pullback.fst g g) :=
    morphismProperty_pullback_fst_self g (@AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hSm2 : AlgebraicGeometry.Smooth (pullback.snd g g) :=
    morphismProperty_pullback_snd_self g (@AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hSu1 : AlgebraicGeometry.Surjective (pullback.fst g g) :=
    morphismProperty_pullback_fst_self g (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hSu2 : AlgebraicGeometry.Surjective (pullback.snd g g) :=
    morphismProperty_pullback_snd_self g (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hFl1 : AlgebraicGeometry.Flat (pullback.fst g g) :=
    morphismProperty_pullback_fst_self g (@AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hFl2 : AlgebraicGeometry.Flat (pullback.snd g g) :=
    morphismProperty_pullback_snd_self g (@AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) inferInstance
      inferInstance
  have hQ1 : AlgebraicGeometry.QuasiCompact (pullback.fst g g) :=
    morphismProperty_pullback_fst_self g (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})
      inferInstance inferInstance
  have hQ2 : AlgebraicGeometry.QuasiCompact (pullback.snd g g) :=
    morphismProperty_pullback_snd_self g (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})
      inferInstance inferInstance
  have hSm1' : AlgebraicGeometry.Smooth (pullback.fst g g) := hSm1
  have hSm2' : AlgebraicGeometry.Smooth (pullback.snd g g) := hSm2
  have hQC1 : AlgebraicGeometry.QuasiCompact (pullback.fst g g ≫ S.structMap) :=
    morphismProperty_comp (pullback.fst g g) S.structMap
      (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u}) inferInstance
      inferInstance inferInstance
  have hQC2 : AlgebraicGeometry.QuasiCompact (pullback.snd g g ≫ S.structMap) :=
    morphismProperty_comp (pullback.snd g g) S.structMap
      (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u}) inferInstance
      inferInstance inferInstance
  have hLF1 : AlgebraicGeometry.LocallyOfFiniteType (pullback.fst g g ≫ S.structMap) :=
    morphismProperty_comp (pullback.fst g g) S.structMap
      (@AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u}) inferInstance
      inferInstance inferInstance
  have hLF2 : AlgebraicGeometry.LocallyOfFiniteType (pullback.snd g g ≫ S.structMap) :=
    morphismProperty_comp (pullback.snd g g) S.structMap
      (@AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u}) inferInstance
      inferInstance inferInstance
  have hcond : pullback.snd g g ≫ g = pullback.fst g g ≫ g := pullback.condition.symm
  have hstruct : pullback.snd g g ≫ S.structMap = pullback.fst g g ≫ S.structMap :=
    hcolS (pullback g g) (pullback.snd g g) (pullback.fst g g) hcond
  have hideal : S.ideal.comap (pullback.snd g g) = S.ideal.comap (pullback.fst g g) :=
    hcolI (pullback g g) (pullback.snd g g) (pullback.fst g g) hcond
  have htriple : LowerDimReductionPullback.pullbackTriple S (pullback.snd g g)
      = LowerDimReductionPullback.pullbackTriple S (pullback.fst g g) :=
    hcol (pullback g g) (pullback.snd g g) (pullback.fst g g) hcond
  have hadm1 : IsMaxContactHypersurface S.base (pullback.fst g g ≫ S.structMap)
      (S.ideal.comap (pullback.fst g g)) S.mult (H.comap (pullback.fst g g)) :=
    hsap S.base S.scheme S.structMap (pullback g g) (pullback.fst g g) S.ideal S.mult
      hSV.one_le_mult H hH
  have hadm2 : IsMaxContactHypersurface S.base (pullback.snd g g ≫ S.structMap)
      (S.ideal.comap (pullback.snd g g)) S.mult (H.comap (pullback.fst g g)) :=
    isMaxContactHypersurface_of_eq_of_eq_of_eq S.base hstruct.symm hideal.symm rfl hadm1
  have hVb : (S.withBoundary [H]).IsAdmissible :=
    { charZero := hSV.charZero
      locallyOfFiniteType := hSV.locallyOfFiniteType
      nonzeroOnComponents := hSV.nonzeroOnComponents
      one_le_mult := hSV.one_le_mult
      quasiCompact := hSV.quasiCompact
      smooth := hSV.smooth
      snc := hHsnc }
  have hsnc1 : InStrictNormalCrossingPosition (pullback.fst g g ≫ S.structMap) [H.comap (pullback.fst g g)] :=
    inStrictNormalCrossingPosition_comap_boundary hin (S.withBoundary [H]) hVb (pullback.fst g g) hSm1 hQC1
  have hsnc2 : InStrictNormalCrossingPosition (pullback.snd g g ≫ S.structMap) [H.comap (pullback.fst g g)] := by
    rw [hstruct]
    exact hsnc1
  have hs1 := isStrictPullbackBlowupSeq_reduceAlongHypersurface_pullback hstar hin hmc hsap hinv P hmono A B hspec T hPdimT
    S hSV hSO hSdim H hH hHsnc (pullback.fst g g) hSm1 hFl1 hSu1 hEt1
    (H.comap (pullback.fst g g)) hadm1 hsnc1
  have hs2 := isStrictPullbackBlowupSeq_reduceAlongHypersurface_pullback hstar hin hmc hsap hinv P hmono A B hspec T hPdimT
    S hSV hSO hSdim H hH hHsnc (pullback.snd g g) hSm2 hFl2 hSu2 hEt2
    (H.comap (pullback.fst g g)) hadm2 hsnc2
  have hseq : (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
        (LowerDimReductionPullback.pullbackTriple S (pullback.snd g g))
        (H.comap (pullback.fst g g))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      = (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
        (LowerDimReductionPullback.pullbackTriple S (pullback.fst g g))
        (H.comap (pullback.fst g g))).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    eq_of_heq (heq_reduceAlongHypersurface_of_eq hinv T (fun S' _ i => A i S') htriple
      (H.comap (pullback.fst g g)) (H.comap (pullback.fst g g))
      (HEq.refl (H.comap (pullback.fst g g))))
  have hs2' : IsStrictPullbackBlowupSeq (pullback.snd g g)
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
        (LowerDimReductionPullback.pullbackTriple S (pullback.fst g g))
        (H.comap (pullback.fst g g))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
    rw [← hseq]
    exact hs2
  have hbc1 : IsStrictPullbackBlowupSeq (pullback.fst g g)
      ((MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
          S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups.baseChange (pullback.fst g g))
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hbc2 : IsStrictPullbackBlowupSeq (pullback.snd g g)
      ((MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
          S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups.baseChange (pullback.snd g g))
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have e1 := hbc1.isomorphic hs1
  have e2 := hbc2.isomorphic hs2'
  obtain ⟨s, hs⟩ := exists_isStrictPullback_of_isomorphic_baseChange g
    (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups
    (e1.trans e2.symm)
  exact ⟨BlowupSequenceData.ofSequenceOfBlowups s, hs.of_isomorphic_base (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic s).symm⟩

theorem exists_isStrictPullback_coverMarkedSequence
    (hstar : MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (hmc : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u})
    (hsap : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
        d.toSequenceOfBlowups := by
  classical
  obtain ⟨d, hd⟩ :=
    exists_isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar hin hmc hsap hinv P hmono A B hspec
      T h.dim_prop
      (MaxContactCoverData.coverTriple T h.valid) (BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P T h)
      (BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P T h)
      (hstar.coverTriple_dim_le T h.valid)
      (MaxContactCoverData.coverMap T h.valid)
      (MaxContactCoverData.etale_coverMap_of_isAdmissible T h.valid)
      (MaxContactCoverData.smooth_coverMap_of_isAdmissible T h.valid)
      (MaxContactCoverData.flat_coverMap_of_isAdmissible T h.valid)
      (MaxContactCoverData.surjective_coverMap T h.valid (hstar.exists_goodCover T h.valid h.orderLE))
      T.structMap rfl
      (MaxContactCoverData.balancedTunedIdeal T h.valid) rfl
      T.boundary rfl
      (MaxContactCoverData.coverMaxContactIdeal T h.valid)
      (by
        intro _inst
        exact BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P T h)
      (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P T h)
  have hcs : MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)
      = MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S')
          (MaxContactCoverData.coverTriple T h.valid)
          (MaxContactCoverData.coverMaxContactIdeal T h.valid) := by
    with_unfolding_all rfl
  refine ⟨d, ?_⟩
  rw [hcs, ← MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups]
  exact hd

end MaxContactCoverDescent

end FunctorialResolution.EmbeddedResolution

end
