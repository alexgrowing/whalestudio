import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeCoproduct
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution.MaxContactCoverGeometry

private theorem map_iInf_of_bijective {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Bijective φ) {ι : Type*} (K : ι → Ideal A) :
    Ideal.map φ (⨅ i, K i) = ⨅ i, Ideal.map φ (K i) :=
  (Ideal.relIsoOfBijective φ hφ).symm.map_iInf K

private theorem bijective_appLE_image {A B : Scheme.{u}} (g : A ⟶ B) [IsOpenImmersion g]
    (S : A.Opens) (e : S ≤ g ⁻¹ᵁ (g ''ᵁ S)) :
    Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appLE g (g ''ᵁ S) S e)) := by
  have : IsIso (Scheme.Hom.appLE g (g ''ᵁ S) S e) := by
    rw [← Scheme.Hom.appIso_hom' g S]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

private theorem ideal_iInf {X : Scheme.{u}} {ι : Type v} [Finite ι]
    (I : ι → X.IdealSheafData) (U : X.affineOpens) :
    (⨅ i, I i).ideal U = ⨅ i, (I i).ideal U := by
  simp only [AlgebraicGeometry.Scheme.IdealSheafData.ideal_iInf, iInf_apply]

theorem comap_iInf {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {ι : Type v} [Finite ι] (J : ι → Y.IdealSheafData) :
    (⨅ i, J i).comap f = ⨅ i, (J i).comap f := by
  refine Scheme.IdealSheafData.ext ?_
  funext V
  have hU : IsAffineOpen (f ''ᵁ (V : X.Opens)) := V.2.image_of_isOpenImmersion f
  have e : (V : X.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : X.Opens)) :=
    (f.preimage_image_eq (V : X.Opens)).ge
  have hbij : Function.Bijective
      (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom :=
    bijective_appLE_image f (V : X.Opens) e
  have key : ∀ I : Y.IdealSheafData, (I.comap f).ideal V =
      (I.ideal ⟨f ''ᵁ (V : X.Opens), hU⟩).map
        (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom := fun I =>
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f ⟨f ''ᵁ (V : X.Opens), hU⟩ V e
  have h1 : (⨅ i, J i).ideal ⟨f ''ᵁ (V : X.Opens), hU⟩
      = ⨅ i, (J i).ideal ⟨f ''ᵁ (V : X.Opens), hU⟩ :=
    ideal_iInf J ⟨f ''ᵁ (V : X.Opens), hU⟩
  have h2 : (⨅ i, (J i).comap f).ideal V = ⨅ i, ((J i).comap f).ideal V :=
    ideal_iInf (fun i => (J i).comap f) V
  rw [h2, key (⨅ i, J i), h1, map_iInf_of_bijective _ hbij]
  exact iInf_congr fun i => (key (J i)).symm

theorem ker_subschemeι_comp_comap_self {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] [QuasiCompact f]
    (I : X.IdealSheafData) :
    ((I.subschemeι ≫ f).ker).comap f = I :=
  FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp I f

theorem ker_subschemeι_comp_comap_eq_top_of_disjoint {X X' Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (g : X' ⟶ Y) [QuasiCompact g]
    (hdisj : ∀ (x : ↥X) (x' : ↥X'), f.base x ≠ g.base x') (J : X'.IdealSheafData) :
    ((J.subschemeι ≫ g).ker).comap f = ⊤ := by
  refine FunctorialResolution.Blowup.comap_eq_top_of_notMem_support f ((J.subschemeι ≫ g).ker) ?_
  intro x hx
  have hx' : f.base x ∈ (((J.subschemeι ≫ g).ker).support : Set ↥Y) := hx
  rw [Scheme.Hom.support_ker] at hx'
  have hopen : IsOpen (Set.range ⇑f.base) := f.isOpenEmbedding.isOpen_range
  obtain ⟨y, hy1, hy2⟩ :=
    mem_closure_iff.mp hx' (Set.range ⇑f.base) hopen (Set.mem_range_self x)
  obtain ⟨x₀, hx₀⟩ := hy1
  obtain ⟨w, hw⟩ := hy2
  have hwe : g.base (J.subschemeι.base w) = y := by
    rw [← hw]
    simp
  exact hdisj x₀ (J.subschemeι.base w) (hx₀.trans hwe.symm)

variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)

instance instIsClosedImmersionStarι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    IsClosedImmersion (MaxContactOpenCover.coverPieceι T hv i) :=
  FunctorialResolution.Blowup.isClosedImmersion_sigmaι
    (fun j : (MaxContactCoverData.chosenCoverData T hv).idx => MaxContactOpenCover.coverPiece T hv j) i

theorem quasiCompact_coverPieceι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    QuasiCompact (MaxContactOpenCover.coverPieceι T hv i) :=
  FunctorialResolution.Blowup.quasiCompact_sigmaι
    (fun j : (MaxContactCoverData.chosenCoverData T hv).idx => MaxContactOpenCover.coverPiece T hv j) i

instance instQuasiCompactStarι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    QuasiCompact (MaxContactOpenCover.coverPieceι T hv i) :=
  quasiCompact_coverPieceι T hv i

theorem coverPieceι_base_ne_of_ne {i j : (MaxContactCoverData.chosenCoverData T hv).idx} (hij : i ≠ j)
    (x : ↥(MaxContactOpenCover.coverPiece T hv i)) (y : ↥(MaxContactOpenCover.coverPiece T hv j)) :
    (MaxContactOpenCover.coverPieceι T hv i).base x ≠ (MaxContactOpenCover.coverPieceι T hv j).base y :=
  FunctorialResolution.Blowup.sigmaι_base_ne
    (fun k : (MaxContactCoverData.chosenCoverData T hv).idx => MaxContactOpenCover.coverPiece T hv k) hij x y

theorem ker_subschemeι_comp_coverPieceι_comap_self (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    ((((MaxContactCoverData.chosenCoverData T hv).localIdeal i).subschemeι ≫
        MaxContactOpenCover.coverPieceι T hv i).ker).comap (MaxContactOpenCover.coverPieceι T hv i) =
      (MaxContactCoverData.chosenCoverData T hv).localIdeal i :=
  ker_subschemeι_comp_comap_self (MaxContactOpenCover.coverPieceι T hv i) _

theorem ker_subschemeι_comp_coverPieceι_comap_of_ne {i j : (MaxContactCoverData.chosenCoverData T hv).idx} (hij : i ≠ j) :
    ((((MaxContactCoverData.chosenCoverData T hv).localIdeal j).subschemeι ≫
        MaxContactOpenCover.coverPieceι T hv j).ker).comap (MaxContactOpenCover.coverPieceι T hv i) = ⊤ :=
  ker_subschemeι_comp_comap_eq_top_of_disjoint (MaxContactOpenCover.coverPieceι T hv i) (MaxContactOpenCover.coverPieceι T hv j)
    (coverPieceι_base_ne_of_ne T hv hij) _

theorem comap_coverMaxContactIdeal_coverPieceι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
      (MaxContactCoverData.chosenCoverData T hv).localIdeal i := by
  have key : (⨅ j : (MaxContactCoverData.chosenCoverData T hv).idx,
      (((MaxContactCoverData.chosenCoverData T hv).localIdeal j).subschemeι ≫
        MaxContactOpenCover.coverPieceι T hv j).ker).comap (MaxContactOpenCover.coverPieceι T hv i) =
      (MaxContactCoverData.chosenCoverData T hv).localIdeal i := by
    rw [comap_iInf]
    refine le_antisymm (le_trans (iInf_le _ i) (le_of_eq (ker_subschemeι_comp_coverPieceι_comap_self T hv i)))
      (le_iInf fun j => ?_)
    rcases eq_or_ne j i with rfl | h
    · exact le_of_eq (ker_subschemeι_comp_coverPieceι_comap_self T hv _).symm
    · rw [ker_subschemeι_comp_coverPieceι_comap_of_ne T hv h.symm]
      exact le_top
  exact key

theorem isMaxContactHypersurface_coverMaxContactIdeal
    [AlgebraicGeometry.LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap]
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)) :
    IsMaxContactHypersurface (MaxContactCoverData.coverTriple T hv).base
      (MaxContactCoverData.coverTriple T hv).structMap (MaxContactCoverData.coverTriple T hv).ideal
      (MaxContactCoverData.tunedMult T) (MaxContactCoverData.coverMaxContactIdeal T hv) :=
  FunctorialResolution.EmbeddedResolution.isMaxContactHypersurface_coverMaxContactIdeal_of_comap_eq T hv hgood (comap_coverMaxContactIdeal_coverPieceι T hv)

theorem inStrictNormalCrossingPositionAt_of_isMaxContactCover
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (x : ↥(MaxContactCoverData.coverTriple T hv).scheme) :
    InStrictNormalCrossingPositionAt (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] x :=
  FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPositionAt_coverMaxContactIdeal T hv hgood (comap_coverMaxContactIdeal_coverPieceι T hv) x

theorem inStrictNormalCrossingPosition_of_isMaxContactCover
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hsm : IsSmoothDivisor (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverMaxContactIdeal T hv)) :
    InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] :=
  FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_coverMaxContactIdeal T hv hgood (comap_coverMaxContactIdeal_coverPieceι T hv) hsm

end FunctorialResolution.EmbeddedResolution.MaxContactCoverGeometry

end
