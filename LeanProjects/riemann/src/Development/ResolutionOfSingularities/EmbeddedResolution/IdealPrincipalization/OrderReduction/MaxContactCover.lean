import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCoordinate
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMapSurjective
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactOpenCover

private theorem isOpenImmersion_fst_of_isPullback
    {P' X' Y' Z' : Scheme.{u}} {p₁ : P' ⟶ X'} {p₂ : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (hsq : IsPullback p₁ p₂ f' g') (hg : IsOpenImmersion g') : IsOpenImmersion p₁ :=
  MorphismProperty.of_isPullback hsq.flip hg

theorem isLocalIsomorphism_fst_of_isPullback {P X Y Z : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hsq : IsPullback fst snd f g)
    (hg : MaxContactFunctoriality.IsLocalIsomorphism g) :
    MaxContactFunctoriality.IsLocalIsomorphism fst := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hg (snd.base x)
  exact ⟨_, hxU, isOpenImmersion_fst_of_isPullback
    ((isPullback_morphismRestrict snd U).flip.paste_horiz hsq) hU⟩

abbrev coverPiece (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) : Scheme.{u} :=
  (((MaxContactCoverData.chosenCoverData T hv).opens i : T.scheme.Opens) : Scheme.{u})

abbrev coverPieceι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    coverPiece T hv i ⟶ (MaxContactCoverData.coverTriple T hv).scheme :=
  Sigma.ι (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
    (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u})) i

theorem isOpenImmersion_coverPieceι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    IsOpenImmersion (coverPieceι T hv i) := by
  have h : IsOpenImmersion (Sigma.ι (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
      (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u})) i) :=
    inferInstance
  exact h

instance instIsOpenImmersionStarι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    IsOpenImmersion (coverPieceι T hv i) :=
  isOpenImmersion_coverPieceι T hv i

abbrev coverTripleOpen (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    (MaxContactCoverData.coverTriple T hv).scheme.Opens :=
  (coverPieceι T hv i).opensRange

abbrev coverTriplePiece (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) : Scheme.{u} :=
  ((coverTripleOpen T hv i : (MaxContactCoverData.coverTriple T hv).scheme.Opens) : Scheme.{u})

theorem range_coverPieceι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    Set.range (coverPieceι T hv i).base = Set.range (coverTripleOpen T hv i).ι.base :=
  ((coverTripleOpen T hv i).range_ι).symm

def coverPieceIso (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    coverPiece T hv i ≅ coverTriplePiece T hv i :=
  IsOpenImmersion.isoOfRangeEq (coverPieceι T hv i) (coverTripleOpen T hv i).ι (range_coverPieceι T hv i)

theorem exists_mem_coverTripleOpen (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (x : ↥(MaxContactCoverData.coverTriple T hv).scheme) :
    ∃ i : (MaxContactCoverData.chosenCoverData T hv).idx, x ∈ coverTripleOpen T hv i := by
  obtain ⟨⟨i, y⟩, hy⟩ := (AlgebraicGeometry.sigmaMk
    (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
      (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u}))).surjective x
  refine ⟨i, ?_⟩
  show x ∈ Set.range (Sigma.ι (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
    (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u})) i).base
  refine ⟨y, ?_⟩
  rw [← hy]
  simp

private theorem coverPieceIso_inv_comp_coverPieceι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    (coverPieceIso T hv i).inv ≫ coverPieceι T hv i = (coverTripleOpen T hv i).ι := by
  apply AlgebraicGeometry.IsOpenImmersion.lift_fac

private theorem coverPieceι_comp_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    coverPieceι T hv i ≫ MaxContactCoverData.coverMap T hv =
      ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := by
  rw [MaxContactCoverData.coverMap_eq_sigmaOpensDesc]
  exact sigma_ι_sigmaOpensDesc T.scheme (MaxContactCoverData.chosenCoverData T hv).opens i

theorem coverTripleOpen_ι_comp_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    (coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv =
      (coverPieceIso T hv i).inv ≫ ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := by
  have h := coverPieceIso_inv_comp_coverPieceι T hv i
  calc (coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv
      = ((coverPieceIso T hv i).inv ≫ coverPieceι T hv i) ≫ MaxContactCoverData.coverMap T hv := by rw [h]
    _ = (coverPieceIso T hv i).inv ≫ (coverPieceι T hv i ≫ MaxContactCoverData.coverMap T hv) :=
        Category.assoc _ _ _
    _ = (coverPieceIso T hv i).inv ≫ ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := by
        rw [coverPieceι_comp_coverMap T hv i]

theorem restrictIdeal_coverTripleOpen (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx)
    (J : (MaxContactCoverData.coverTriple T hv).scheme.IdealSheafData) :
    restrictIdeal J (coverTripleOpen T hv i) = (J.comap (coverPieceι T hv i)).comap (coverPieceIso T hv i).inv := by
  simp only [restrictIdeal_eq_comap_ι, ← coverPieceIso_inv_comp_coverPieceι T hv i,
    Scheme.IdealSheafData.comap_comp]

theorem isLocalIsomorphism_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    MaxContactFunctoriality.IsLocalIsomorphism (MaxContactCoverData.coverMap T hv) := by
  intro x
  obtain ⟨i, hxi⟩ := exists_mem_coverTripleOpen T hv x
  have hψ : IsOpenImmersion ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) := by
    rw [coverTripleOpen_ι_comp_coverMap T hv i]
    infer_instance
  exact ⟨coverTripleOpen T hv i, hxi, hψ⟩

private theorem coverPieceIso_inv_comp_map_comp_affineSpaceFinToSpec (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n) :
    ((coverPieceIso T hv i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n =
      (coverTripleOpen T hv i).ι ≫ (MaxContactCoverData.coverMap T hv ≫ T.structMap) := by
  have h1 : c.map ≫ affineSpaceFinToSpec T.base n =
      ((MaxContactCoverData.chosenCoverData T hv).opens i).ι ≫ T.structMap := c.comp_struct
  have h2 := coverTripleOpen_ι_comp_coverMap T hv i
  calc ((coverPieceIso T hv i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n
      = (coverPieceIso T hv i).inv ≫ (c.map ≫ affineSpaceFinToSpec T.base n) := Category.assoc _ _ _
    _ = (coverPieceIso T hv i).inv ≫ (((MaxContactCoverData.chosenCoverData T hv).opens i).ι ≫ T.structMap) := by
        rw [h1]
    _ = ((coverPieceIso T hv i).inv ≫ ((MaxContactCoverData.chosenCoverData T hv).opens i).ι) ≫ T.structMap :=
        (Category.assoc _ _ _).symm
    _ = ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) ≫ T.structMap := by rw [h2]
    _ = (coverTripleOpen T hv i).ι ≫ (MaxContactCoverData.coverMap T hv ≫ T.structMap) :=
        Category.assoc _ _ _

private theorem etale_coverPieceIso_inv_comp_map (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n) :
    AlgebraicGeometry.Etale ((coverPieceIso T hv i).inv ≫ c.map) := by
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  have : IsIso (coverPieceIso T hv i).inv := inferInstance
  have : IsOpenImmersion (coverPieceIso T hv i).inv := inferInstance
  have : AlgebraicGeometry.Etale (coverPieceIso T hv i).inv := inferInstance
  infer_instance

def coverEtaleChart (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n) :
    EtaleChart (MaxContactCoverData.coverMap T hv ≫ T.structMap) (coverTripleOpen T hv i) n where
  map := (coverPieceIso T hv i).inv ≫ c.map
  comp_struct := coverPieceIso_inv_comp_map_comp_affineSpaceFinToSpec T hv i c
  isEtale := etale_coverPieceIso_inv_comp_map T hv i c

theorem coverEtaleChart_coordIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n)
    (S : Finset (Fin n)) :
    (coverEtaleChart T hv i c).coordIdeal S = (c.coordIdeal S).comap (coverPieceIso T hv i).inv := by
  have key : (coordSubspaceIdeal T.base n S).comap ((coverPieceIso T hv i).inv ≫ c.map)
      = ((coordSubspaceIdeal T.base n S).comap c.map).comap (coverPieceIso T hv i).inv := by
    rw [Scheme.IdealSheafData.comap_comp]
  have h1 : (coverEtaleChart T hv i c).coordIdeal S
      = (coordSubspaceIdeal T.base n S).comap ((coverPieceIso T hv i).inv ≫ c.map) :=
    EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal (coverEtaleChart T hv i c) S
  have h2 : (c.coordIdeal S).comap (coverPieceIso T hv i).inv
      = ((coordSubspaceIdeal T.base n S).comap c.map).comap (coverPieceIso T hv i).inv :=
    congrArg (fun J => J.comap (coverPieceIso T hv i).inv) (EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal c S)
  exact h1.trans (key.trans h2.symm)

private theorem compactSpace_of_quasiCompact_toSpec {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (hf : AlgebraicGeometry.QuasiCompact f) : CompactSpace ↥X := by
  have := hf
  exact QuasiCompact.compactSpace_of_compactSpace f

private theorem exists_affineOpen_maxContactCoord_or_disjoint_locus (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (h : ∀ x : ↥T.scheme,
      orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x ≤ ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞))
    (x : ↥T.scheme) :
    ∃ (V : T.scheme.Opens) (J : (V : Scheme.{u}).IdealSheafData),
      x ∈ V ∧ AlgebraicGeometry.IsAffineOpen V ∧
        ((Disjoint (orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
              (V : Set ↥T.scheme) ∧ J = ⊤) ∨
          ∃ (n : ℕ) (c : EtaleChart T.structMap V n) (j : Fin n),
            J = c.coordIdeal {j} ∧
              MaxContactReduction.IsMaxContactCoord T.base T.structMap
                (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) c j) := by
  classical
  have := hv.charZero
  have := hv.smooth
  have hm : 1 ≤ MaxContactCoverData.tunedMult T := one_le_tuningExponent T.mult
  by_cases hx : x ∈ orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)
  · have hord : orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x
        = ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞) :=
      le_antisymm (h x) ((mem_orderAtLeastLocus_iff _ _ _).1 hx)
    obtain ⟨V, hVaff, hxV, n, c, j, hmc, -⟩ :=
      exists_isMaxContactCoord T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv) hm x hord
    exact ⟨V, c.coordIdeal {j}, hxV, hVaff, Or.inr ⟨n, c, j, rfl, hmc⟩⟩
  · have hcl : IsClosed
        (orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)) :=
      isClosed_orderAtLeastLocus T.base T.structMap _ _
    obtain ⟨V, n, hxV, hVW, hVaff, -⟩ :=
      exists_etaleChart_le T.structMap x
        ⟨(orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))ᶜ,
          hcl.isOpen_compl⟩ hx
    refine ⟨V, ⊤, hxV, hVaff, Or.inl ⟨?_, rfl⟩⟩
    refine Set.disjoint_left.2 ?_
    intro y hyS hyV
    exact (hVW hyV) hyS

theorem exists_isMaxContactCover (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (h : ∀ x : ↥T.scheme,
      orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x ≤ ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞)) :
    ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
      MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType (MaxContactCoverData.balancedTunedIdeal T hv)
        (MaxContactCoverData.tunedMult T) := by
  classical
  have := hv.locallyOfFiniteType
  have : CompactSpace ↥T.scheme := compactSpace_of_quasiCompact_toSpec T.structMap hv.quasiCompact
  choose V J hxV hVaff hdich using exists_affineOpen_maxContactCoord_or_disjoint_locus T hv h
  have hcover : (Set.univ : Set ↥T.scheme) ⊆
      ⋃ x : ↥T.scheme, ((V x : T.scheme.Opens) : Set ↥T.scheme) := by
    intro y _
    exact Set.mem_iUnion.2 ⟨y, hxV y⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : ↥T.scheme => ((V x : T.scheme.Opens) : Set ↥T.scheme))
    (fun x => (V x).isOpen) hcover
  refine ⟨{ idx := {y : ↥T.scheme // y ∈ t},
            finiteIdx := inferInstance,
            opens := fun i => V i.1,
            localIdeal := fun i => J i.1 }, ?_, ?_, ?_⟩
  · refine le_antisymm le_top ?_
    intro y _
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hyi⟩
  · exact fun i => hVaff i.1
  · exact fun i => hdich i.1

def tunedTriple (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) : MarkedIdealWithBoundary.{u} where
  base := T.base
  scheme := T.scheme
  structMap := T.structMap
  ideal := MaxContactCoverData.balancedTunedIdeal T hv
  mult := MaxContactCoverData.tunedMult T
  boundary := T.boundary

@[simp] theorem tunedTriple_baseField (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).base = T.base := rfl

@[simp] theorem tunedTriple_scheme (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).scheme = T.scheme := rfl

@[simp] theorem tunedTriple_structureMorphism (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).structMap = T.structMap := rfl

@[simp] theorem tunedTriple_ideal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).ideal = MaxContactCoverData.balancedTunedIdeal T hv := rfl

@[simp] theorem tunedTriple_mult (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).mult = MaxContactCoverData.tunedMult T := rfl

@[simp] theorem tunedTriple_boundary (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).boundary = T.boundary := rfl

theorem isAdmissible_tunedTriple (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hnz : NonzeroOnComponents (MaxContactCoverData.balancedTunedIdeal T hv)) :
    (tunedTriple T hv).IsAdmissible :=
  { charZero := hv.charZero
    locallyOfFiniteType := hv.locallyOfFiniteType
    nonzeroOnComponents := hnz
    one_le_mult := one_le_tuningExponent T.mult
    quasiCompact := hv.quasiCompact
    smooth := hv.smooth
    snc := hv.snc }

theorem coverTriple_eq_tunedTriple_pullbackAlong (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    MaxContactCoverData.coverTriple T hv =
      (tunedTriple T hv).pullbackAlong (MaxContactCoverData.chosenCoverData T hv).disjointUnion
        (MaxContactCoverData.coverMap T hv ≫ T.structMap) (MaxContactCoverData.coverMap T hv) :=
  rfl

theorem isAffine_coverTriple_scheme (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)) :
    AlgebraicGeometry.IsAffine (MaxContactCoverData.coverTriple T hv).scheme :=
  isAffine_sigmaOpens T.scheme (MaxContactCoverData.chosenCoverData T hv).opens hgood.isAffine

theorem quasiCompact_coverMap_comp_structureMorphism (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)) :
    AlgebraicGeometry.QuasiCompact (MaxContactCoverData.coverMap T hv ≫ T.structMap) := by
  have : AlgebraicGeometry.IsAffine ((MaxContactCoverData.chosenCoverData T hv).disjointUnion) :=
    isAffine_coverTriple_scheme T hv hgood
  have : AlgebraicGeometry.IsAffine (MaxContactCoverData.coverTriple T hv).scheme :=
    isAffine_coverTriple_scheme T hv hgood
  have : Subsingleton ↥(AlgebraicGeometry.Spec (CommRingCat.of T.base)) := inferInstance
  constructor
  intro U _hU _hUc
  by_cases hUe : U = ∅
  · subst hUe
    rw [Set.preimage_empty]
    exact isCompact_empty
  · have hUu : U = Set.univ := by
      obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hUe
      refine Set.eq_univ_of_forall fun z => ?_
      rwa [Subsingleton.elim z u]
    subst hUu
    rw [Set.preimage_univ]
    exact isCompact_univ

private theorem isEmpty_irreducibleCloseds_of_isEmpty {C : Type u} [TopologicalSpace C] (h : IsEmpty C) :
    IsEmpty (TopologicalSpace.IrreducibleCloseds C) :=
  ⟨fun Z => h.elim Z.2.1.choose⟩

private theorem topologicalKrullDim_le_of_isEmpty {C B : Type u} [TopologicalSpace C]
    [TopologicalSpace B] (h : IsEmpty C) :
    topologicalKrullDim C ≤ topologicalKrullDim B := by
  have := isEmpty_irreducibleCloseds_of_isEmpty h
  show Order.krullDim (TopologicalSpace.IrreducibleCloseds C)
      ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds B)
  exact Order.krullDim_le_of_strictMono
    (fun Z : TopologicalSpace.IrreducibleCloseds C => isEmptyElim Z)
    (fun a _ _ => isEmptyElim a)

private theorem topologicalKrullDim_ne_bot {B : Type u} [TopologicalSpace B] (b : B) :
    topologicalKrullDim B ≠ ⊥ := by
  intro hb
  have hb' : Order.krullDim (TopologicalSpace.IrreducibleCloseds B) = ⊥ := hb
  have hE : IsEmpty (TopologicalSpace.IrreducibleCloseds B) := Order.krullDim_eq_bot_iff.mp hb'
  exact hE.elim ⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩

private theorem topologicalKrullDim_le_of_isOpenImmersion {P Q : Scheme.{u}} (f : P ⟶ Q)
    (h : IsOpenImmersion f) : topologicalKrullDim ↥P ≤ topologicalKrullDim ↥Q := by
  have := h
  exact f.isOpenEmbedding.isInducing.topologicalKrullDim_le

private theorem topologicalKrullDim_coverTripleOpen_le (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    topologicalKrullDim
        ↥(↑(coverTripleOpen T hv i) : Set ↥(MaxContactCoverData.coverTriple T hv).scheme)
      ≤ topologicalKrullDim ↥T.scheme := by
  have hψ : IsOpenImmersion ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) := by
    rw [coverTripleOpen_ι_comp_coverMap T hv i]
    infer_instance
  exact topologicalKrullDim_le_of_isOpenImmersion
    ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) hψ

theorem krullDimSucc_coverTriple_scheme_le_dim (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    krullDimSucc (MaxContactCoverData.coverTriple T hv).scheme ≤ T.krullDimSucc := by
  have hd : topologicalKrullDim ↥T.scheme < ⊤ := hv.topologicalKrullDim_lt_top
  by_cases hTe : IsEmpty ↥T.scheme
  · have hce : IsEmpty ↥(MaxContactCoverData.coverTriple T hv).scheme :=
      ⟨fun x => hTe.elim ((MaxContactCoverData.coverMap T hv).base x)⟩
    exact krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _
      (topologicalKrullDim_le_of_isEmpty hce) hd
  · obtain ⟨y⟩ : Nonempty ↥T.scheme := not_isEmpty_iff.mp hTe
    have hbot : topologicalKrullDim ↥T.scheme ≠ ⊥ := topologicalKrullDim_ne_bot y
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
    have hmtop : m ≠ ⊤ := by
      rintro rfl
      rw [WithBot.coe_top] at hm
      rw [← hm] at hd
      exact lt_irrefl _ hd
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hmtop
    have hdeq : topologicalKrullDim ↥T.scheme = ((k : ℕ) : WithBot ℕ∞) := by
      rw [← hm, ← hk]
      norm_cast
    refine krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _ ?_ hd
    rw [hdeq]
    refine topologicalKrullDim_le_natCast_of_isOpenCover
      (fun i : (MaxContactCoverData.chosenCoverData T hv).idx =>
        (↑(coverTripleOpen T hv i) : Set ↥(MaxContactCoverData.coverTriple T hv).scheme))
      (fun i => (coverTripleOpen T hv i).isOpen) ?_ k ?_
    · refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨i, hi⟩ := exists_mem_coverTripleOpen T hv x
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro i
      have hpiece := topologicalKrullDim_coverTripleOpen_le T hv i
      rw [hdeq] at hpiece
      exact hpiece

end MaxContactOpenCover

end FunctorialResolution.EmbeddedResolution

end
