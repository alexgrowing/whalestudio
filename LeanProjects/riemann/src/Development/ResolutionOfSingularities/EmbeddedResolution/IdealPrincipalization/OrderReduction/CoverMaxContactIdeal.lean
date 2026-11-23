import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMapSurjective
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem comapEtale_map_comp_affineSpaceFinToSpec {k : Type u} [Field k] {X Y : Scheme.{u}}
    {q : Y ⟶ Spec (CommRingCat.of k)} (g : X ⟶ Y) {U : Y.Opens} {n : ℕ}
    (c : EtaleChart q U n) :
    (morphismRestrict g U ≫ c.map) ≫ affineSpaceFinToSpec k n =
      AlgebraicGeometry.Scheme.Opens.ι ((TopologicalSpace.Opens.map g.base).obj U) ≫ (g ≫ q) := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, morphismRestrict_ι, Category.assoc]

private theorem etale_comapEtale_map {k : Type u} [Field k] {X Y : Scheme.{u}}
    {q : Y ⟶ Spec (CommRingCat.of k)} (g : X ⟶ Y) [AlgebraicGeometry.Etale g]
    {U : Y.Opens} {n : ℕ} (c : EtaleChart q U n) :
    AlgebraicGeometry.Etale (morphismRestrict g U ≫ c.map) := by
  have := c.isEtale
  infer_instance

def EtaleChart.comapEtale {k : Type u} [Field k] {X Y : Scheme.{u}}
    {q : Y ⟶ Spec (CommRingCat.of k)} (g : X ⟶ Y) [AlgebraicGeometry.Etale g]
    {U : Y.Opens} {n : ℕ} (c : EtaleChart q U n) :
    EtaleChart (g ≫ q) ((TopologicalSpace.Opens.map g.base).obj U) n where
  map := morphismRestrict g U ≫ c.map
  comp_struct := comapEtale_map_comp_affineSpaceFinToSpec g c
  isEtale := etale_comapEtale_map g c

@[simp] theorem EtaleChart.comapEtale_map {k : Type u} [Field k] {X Y : Scheme.{u}}
    {q : Y ⟶ Spec (CommRingCat.of k)} (g : X ⟶ Y) [AlgebraicGeometry.Etale g]
    {U : Y.Opens} {n : ℕ} (c : EtaleChart q U n) :
    (EtaleChart.comapEtale g c).map = morphismRestrict g U ≫ c.map := rfl

private theorem range_ι_base_subset {X : Scheme.{u}} (U : X.Opens) :
    Set.range U.ι.base ⊆ (U : Set ↥X) :=
  (Scheme.Opens.range_ι U).subset

private theorem comap_comap_eq_of_comp_eq {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Z) (a' : W ⟶ Y)
    (b' : Y ⟶ Z) (hsq : a ≫ b = a' ≫ b') (I : Z.IdealSheafData) :
    (I.comap b).comap a = (I.comap b').comap a' := by
  have h1 : (I.comap b).comap a = I.comap (a ≫ b) := by
    simp [Scheme.IdealSheafData.comap_comp]
  have h2 : (I.comap b').comap a' = I.comap (a' ≫ b') := by
    simp [Scheme.IdealSheafData.comap_comp]
  rw [h1, h2, hsq]

private theorem restrictIdeal_coverTripleOpen_coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    @restrictIdeal (MaxContactCoverData.coverTriple T hv).scheme
        (MaxContactCoverData.coverMaxContactIdeal T hv) (MaxContactOpenCover.coverTripleOpen T hv i) =
      ((MaxContactCoverData.chosenCoverData T hv).localIdeal i).comap (MaxContactOpenCover.coverPieceIso T hv i).inv :=
  (MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i (MaxContactCoverData.coverMaxContactIdeal T hv)).trans
    (congrArg (fun J : (MaxContactOpenCover.coverPiece T hv i).IdealSheafData =>
      J.comap (MaxContactOpenCover.coverPieceIso T hv i).inv) (hres i))

theorem isMaxContactHypersurface_coverMaxContactIdeal_of_comap_eq (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    [AlgebraicGeometry.LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap]
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i) :
    IsMaxContactHypersurface (MaxContactCoverData.coverTriple T hv).base
      (MaxContactCoverData.coverTriple T hv).structMap (MaxContactCoverData.coverTriple T hv).ideal
      (MaxContactCoverData.tunedMult T) (MaxContactCoverData.coverMaxContactIdeal T hv) := by
  have := hv.charZero
  have := hv.smooth
  have := hv.locallyOfFiniteType
  have hftc : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.coverMap T hv ≫ T.structMap) :=
    (inferInstance : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.coverTriple T hv).structMap)
  intro x
  obtain ⟨i, hxi⟩ := MaxContactOpenCover.exists_mem_coverTripleOpen T hv x
  have hAff0 : AlgebraicGeometry.IsAffine (MaxContactOpenCover.coverPiece T hv i) := hgood.isAffine i
  have haffineOpen : IsAffineOpen (MaxContactOpenCover.coverTripleOpen T hv i) :=
    isAffineOpen_opensRange (MaxContactOpenCover.coverPieceι T hv i)
  refine ⟨MaxContactOpenCover.coverTripleOpen T hv i, haffineOpen, hxi, ?_⟩
  have hcompι : MaxContactOpenCover.coverPieceι T hv i ≫ MaxContactCoverData.coverMap T hv =
      ((MaxContactCoverData.chosenCoverData T hv).opens i).ι :=
    sigma_ι_sigmaOpensDesc T.scheme (MaxContactCoverData.chosenCoverData T hv).opens i
  have hsub : ∀ y : ↥(MaxContactCoverData.coverTriple T hv).scheme,
      y ∈ (↑(MaxContactOpenCover.coverTripleOpen T hv i) :
        Set ↥(MaxContactCoverData.coverTriple T hv).scheme) →
      (MaxContactCoverData.coverMap T hv).base y ∈
        (↑((MaxContactCoverData.chosenCoverData T hv).opens i) : Set ↥T.scheme) := by
    intro y hy
    have hy' : y ∈ Set.range (MaxContactOpenCover.coverPieceι T hv i).base := hy
    obtain ⟨z, rfl⟩ := hy'
    have hz : (MaxContactCoverData.coverMap T hv).base ((MaxContactOpenCover.coverPieceι T hv i).base z) =
        ((MaxContactCoverData.chosenCoverData T hv).opens i).ι.base z := by
      rw [← hcompι]
      rfl
    rw [hz]
    exact range_ι_base_subset _ ⟨z, rfl⟩
  rcases hgood.dichotomy i with ⟨hdisj, htop⟩ | ⟨n, c, j, hloc, hmc⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro y hy hy2
      have hy3 : y ∈ orderAtLeastLocus
          ((MaxContactCoverData.balancedTunedIdeal T hv).comap (MaxContactCoverData.coverMap T hv))
          (MaxContactCoverData.tunedMult T) := hy
      rw [orderAtLeastLocus_comap T.base T.structMap (MaxContactCoverData.coverMap T hv)
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)] at hy3
      have hy4 : (MaxContactCoverData.coverMap T hv).base y ∈
          orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) := hy3
      exact (Set.disjoint_left.mp hdisj) hy4 (hsub y hy2)
    · rw [restrictIdeal_coverTripleOpen_coverMaxContactIdeal T hv hres i, htop]
      exact Scheme.IdealSheafData.comap_top _
  · right
    refine ⟨n, MaxContactOpenCover.coverEtaleChart T hv i c, j, ?_, ?_⟩
    · rw [restrictIdeal_coverTripleOpen_coverMaxContactIdeal T hv hres i, hloc]
      exact (MaxContactOpenCover.coverEtaleChart_coordIdeal T hv i c {j}).symm
    · have hmc' : c.coordIdeal {j} ≤
          (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap
            ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := hmc
      have hmax : maxContactIdeal (MaxContactCoverData.coverTriple T hv).base
            (MaxContactCoverData.coverTriple T hv).structMap
            (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T) =
          (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap (MaxContactCoverData.coverMap T hv) :=
        derivIdealSheafIterate_comap T.base T.structMap (MaxContactCoverData.coverMap T hv)
          (MaxContactCoverData.tunedMult T - 1) (MaxContactCoverData.balancedTunedIdeal T hv)
      have h1 : (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j}
          = (c.coordIdeal {j}).comap (MaxContactOpenCover.coverPieceIso T hv i).inv :=
        MaxContactOpenCover.coverEtaleChart_coordIdeal T hv i c {j}
      have h2 := comap_comap_eq_of_comp_eq (MaxContactOpenCover.coverTripleOpen T hv i).ι
        (MaxContactCoverData.coverMap T hv)
        (MaxContactOpenCover.coverPieceIso T hv i).inv ((MaxContactCoverData.chosenCoverData T hv).opens i).ι
        (MaxContactOpenCover.coverTripleOpen_ι_comp_coverMap T hv i)
        (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
          (MaxContactCoverData.tunedMult T))
      have h3 : (c.coordIdeal {j}).comap (MaxContactOpenCover.coverPieceIso T hv i).inv ≤
          ((maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap
              ((MaxContactCoverData.chosenCoverData T hv).opens i).ι).comap
            (MaxContactOpenCover.coverPieceIso T hv i).inv :=
        Scheme.IdealSheafData.comap_mono _ hmc'
      show (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j} ≤
        restrictIdeal (maxContactIdeal (MaxContactCoverData.coverTriple T hv).base
          (MaxContactCoverData.coverTriple T hv).structMap
          (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T))
          (MaxContactOpenCover.coverTripleOpen T hv i)
      rw [hmax]
      exact (le_of_eq h1).trans (le_of_le_of_eq h3 h2.symm)

theorem inStrictNormalCrossingPositionAt_coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i)
    (x : ↥(MaxContactCoverData.coverTriple T hv).scheme) :
    InStrictNormalCrossingPositionAt (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] x := by
  obtain ⟨i, hxi⟩ := MaxContactOpenCover.exists_mem_coverTripleOpen T hv x
  have h1 := MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i (MaxContactCoverData.coverMaxContactIdeal T hv)
  rcases hgood.dichotomy i with ⟨_hdisj, htop⟩ | ⟨n, c, j, hlocal, _hmc⟩
  · have h2 : ((MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i)).comap
        (MaxContactOpenCover.coverPieceIso T hv i).inv = ⊤ := by
      rw [hres i, htop]
      exact Scheme.IdealSheafData.comap_top _
    have key := h1.trans h2
    have hsm : AlgebraicGeometry.Smooth (MaxContactCoverData.coverTriple T hv).structMap := by
      have := MaxContactCoverData.smooth_coverMap_of_isAdmissible T hv
      have := hv.smooth
      exact (inferInstance : AlgebraicGeometry.Smooth
        (MaxContactCoverData.coverMap T hv ≫ T.structMap))
    obtain ⟨U, m, hxU, hUle, -, ⟨ch⟩⟩ :=
      exists_etaleChart_le (MaxContactCoverData.coverTriple T hv).structMap x
        (MaxContactOpenCover.coverTripleOpen T hv i) hxi
    have keyU : restrictIdeal (MaxContactCoverData.coverMaxContactIdeal T hv) U = ⊤ := by
      apply restrictIdeal_eq_top_of_le <;> assumption
    refine inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨U, hxU, m, ch, fun _ => none, ?_, ?_, ?_⟩
    · intro r _hr s _hs t hrt _hst
      simp at hrt
    · intro r hr _hnone
      have hr1 : r < 1 := by simpa using hr
      have hr0 : r = 0 := by omega
      subst hr0
      exact keyU
    · intro r _hr t hrt
      simp at hrt
  · have h2 : ((MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i)).comap
        (MaxContactOpenCover.coverPieceIso T hv i).inv = (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j} := by
      rw [hres i, hlocal, MaxContactOpenCover.coverEtaleChart_coordIdeal]
    have key := h1.trans h2
    refine inStrictNormalCrossingPositionAt_of_exists_etaleChart
      ⟨MaxContactOpenCover.coverTripleOpen T hv i, hxi, n, MaxContactOpenCover.coverEtaleChart T hv i c, fun _ => some j,
        ?_, ?_, ?_⟩
    · intro r hr s hs t _hrt _hst
      have hr1 : r < 1 := by simpa using hr
      have hs1 : s < 1 := by simpa using hs
      omega
    · intro r _hr hnone
      simp at hnone
    · intro r hr t hrt
      have hr1 : r < 1 := by simpa using hr
      have hr0 : r = 0 := by omega
      subst hr0
      obtain rfl : j = t := Option.some.inj hrt
      exact key

theorem inStrictNormalCrossingPosition_coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i)
    (hsm : IsSmoothDivisor (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverMaxContactIdeal T hv)) :
    InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] := by
  refine (inStrictNormalCrossingPosition_iff _ _).mpr
    ⟨?_, fun x => inStrictNormalCrossingPositionAt_coverMaxContactIdeal T hv hgood hres x⟩
  intro D hD
  have hD' : D = MaxContactCoverData.coverMaxContactIdeal T hv := List.mem_singleton.mp hD
  subst hD'
  exact hsm

end FunctorialResolution.EmbeddedResolution

end
