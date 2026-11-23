import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCoordinate
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.AppendIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IndependenceOfHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusAfterReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem maxContactIdeal_comap (k : Type u) [Field k] {P Y : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p]
    (g : Y ⟶ P) [AlgebraicGeometry.Smooth g]
    [AlgebraicGeometry.LocallyOfFiniteType (g ≫ p)]
    (A : P.IdealSheafData) (μ : ℕ) :
    maxContactIdeal k (g ≫ p) (A.comap g) μ = (maxContactIdeal k p A μ).comap g := by
  unfold maxContactIdeal
  exact derivIdealSheafIterate_comap k p g (μ - 1) A

namespace BoundarySeparationBaseChange

def IsMaxContactInvariantBalancedTuned : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    (A : P.IdealSheafData) (μ : ℕ), 1 ≤ μ → MaxOrderEq A μ →
      IsMaxContactInvariant k p (balancedTunedSheaf k p A μ) (tuningExponent μ)

def MaxContactHypersurfaceSmoothPullback : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    (Y : Scheme.{u}) (g : Y ⟶ P) [AlgebraicGeometry.Smooth g]
    [AlgebraicGeometry.LocallyOfFiniteType (g ≫ p)]
    (A : P.IdealSheafData) (μ : ℕ), 1 ≤ μ →
      ∀ H : P.IdealSheafData, IsMaxContactHypersurface k p A μ H →
        IsMaxContactHypersurface k (g ≫ p) (A.comap g) μ (H.comap g)

theorem isLocallyNoetherian_schemeAt (_hMaxContact : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) :
    ∀ i ≤ s.length, AlgebraicGeometry.IsLocallyNoetherian (s.obj i) := by
  intro i hi
  have hnoeth : AlgebraicGeometry.IsNoetherian (s.toMarkedSequenceOfBlowups.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i
      (s.le_toSequenceOfBlowups_length hi)
  show AlgebraicGeometry.IsLocallyNoetherian (s.toMarkedSequenceOfBlowups.schemeAt i)
  infer_instance

theorem isAdmissible_derivedTriple_nil (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) :
    (MaxContactCoverData.derivedTriple S s hft ([] : List (s.obj s.length).IdealSheafData) 0).IsAdmissible := by
  refine BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV s hft [] 0 ?_
  have hlev : (S.transformAt s.toMarkedSequenceOfBlowups s.length).IsAdmissible :=
    MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups s.length
      (s.le_toSequenceOfBlowups_length (le_refl s.length))
  have h := hlev.snc
  rw [MarkedIdealWithBoundary.transformAt_structureMorphism, MarkedIdealWithBoundary.transformAt_boundary,
    MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedBlowupSequenceData.toMarkedSequence_projectionToBase] at h
  exact h

theorem orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) :
    ∀ D ∈ (s.boundary s.length).take 0,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (D.support : Set ↥(s.obj s.length)) = ∅ := by
  intro D hD
  simp at hD

private theorem exists_index_of_mem_take {α : Type*} :
    ∀ (L : List α) (n : ℕ) (D : α), D ∈ L.take n →
      ∃ i, ∃ hi : i < L.length, i < n ∧ L.get ⟨i, hi⟩ = D := by
  intro L
  induction L with
  | nil =>
    intro n D hD
    simp at hD
  | cons a t ih =>
    intro n D hD
    cases n with
    | zero => simp at hD
    | succ m =>
      have hD' : D ∈ a :: t.take m := hD
      rcases List.mem_cons.mp hD' with rfl | hD''
      · exact ⟨0, by simp, Nat.succ_pos m, rfl⟩
      · obtain ⟨i, hi, hin, hget⟩ := ih m D hD''
        exact ⟨i + 1, Nat.succ_lt_succ hi, Nat.succ_lt_succ hin, hget⟩

theorem orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (n : ℕ)
    (h : BoundarySeparationByMaxContact.BoundarySeparated S s n) :
    ∀ D ∈ (s.boundary s.length).take n,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (D.support : Set ↥(s.obj s.length)) = ∅ := by
  intro D hD
  obtain ⟨i, hi, hin, hget⟩ := exists_index_of_mem_take (s.boundary s.length) n D hD
  have key := h i hin hi
  rw [hget] at key
  exact key

theorem lt_length_nil_append_boundary_drop_zero (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (j : ℕ)
    (hj : j < S.boundary.length) :
    j < (([] : List (s.obj s.length).IdealSheafData) ++ (s.boundary s.length).drop 0).length := by
  have h1 : s.boundaryFrom S.boundary s.length = s.boundary s.length :=
    MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq s s.length le_rfl
  have h2 : s.boundaryFrom S.boundary s.length
      = S.boundary.map (s.toBlowupSequenceData.iteratedStrictTransform s.length) ++
        s.boundaryFrom ([] : List S.scheme.IdealSheafData) s.length :=
    BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append s.toBlowupSequenceData S.boundary s.length
  have h5 : S.boundary.length ≤ (s.boundary s.length).length := by
    rw [← h1, h2]
    simp only [List.length_append, List.length_map]
    omega
  simp only [List.nil_append, List.drop_zero]
  omega

theorem orderAt_pullbackTriple_le_mult (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
    [AlgebraicGeometry.Smooth q] (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) :
    ∀ x : ↥(LowerDimReductionPullback.pullbackTriple S q).scheme,
      orderAt (LowerDimReductionPullback.pullbackTriple S q).ideal x ≤ (((LowerDimReductionPullback.pullbackTriple S q).mult : ℕ) : ℕ∞) := by
  have : CharZero S.base := hV.charZero
  have : AlgebraicGeometry.Smooth S.structMap := hV.smooth
  intro x
  have h : orderAt (S.ideal.comap q) x = orderAt S.ideal (q x) :=
    orderAt_comap S.base S.structMap q S.ideal x
  exact le_trans (le_of_eq h) (hO (q x))

abbrev separateBoundaryOfFamily (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) (S : MarkedIdealWithBoundary.{u}) (n : ℕ) :
    MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
  MaxContactReduction.separateBoundary hinv T (fun S' _ i => A i S') S n

theorem separateBoundaryInvariant_separateBoundaryOfFamily (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : S.scheme.IdealSheafData) (hH : InStrictNormalCrossingPosition S.structMap [H])
    (j : ℕ) (hj : j ≤ S.boundary.length) :
    BoundarySeparationByMaxContact.SeparateBoundaryInvariant S H (separateBoundaryOfFamily hinv T A S j) j := by
  revert hj
  induction j with
  | zero =>
      intro _
      show BoundarySeparationByMaxContact.SeparateBoundaryInvariant S H (separateBoundaryOfFamily hinv T A S 0) 0
      have h0 : separateBoundaryOfFamily hinv T A S 0
          = emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
        MaxContactCoverData.separateBoundary_zero hinv T (fun S' _ i => A i S') S
      have h1 : (separateBoundaryOfFamily hinv T A S 0).toBlowupSequenceData = BlowupSequenceData.empty S.scheme :=
        Eq.trans
          (congrArg
            (fun s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary => s.toBlowupSequenceData) h0)
          (emptyMarkedBlowupSequenceData_toBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
      have hlen : (separateBoundaryOfFamily hinv T A S 0).length = 0 :=
        Eq.trans (congrArg (fun d : BlowupSequenceData S.scheme => d.length) h1)
          (BlowupSequenceData.empty_length S.scheme)
      refine And.intro ?_ (And.intro ?_ ?_)
      · intro i hi
        exact absurd hi (Nat.not_lt_zero i)
      · intro i hi
        exact absurd hi (by omega)
      · exact BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_iteratedStrictTransform_zero S (separateBoundaryOfFamily hinv T A S 0) H hH
  | succ n ih =>
      intro hj
      show BoundarySeparationByMaxContact.SeparateBoundaryInvariant S H (separateBoundaryOfFamily hinv T A S (n + 1)) (n + 1)
      have hjn : n < S.boundary.length := Nat.lt_of_succ_le hj
      have key : BoundarySeparationByMaxContact.SeparateBoundaryInvariant S H
          (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S
            (separateBoundaryOfFamily hinv T A S n) [] 0 n) (n + 1) :=
        BoundarySeparationByMaxContact.separateBoundaryInvariant_appendLowerDimReduction hstar hinv P hmono A B hspec T hPdimT S hV hO
          hdimS H hH (separateBoundaryOfFamily hinv T A S n) n hjn (ih (Nat.le_of_succ_le hj))
      have hstep : separateBoundaryOfFamily hinv T A S (n + 1)
          = MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S
              (separateBoundaryOfFamily hinv T A S n) [] 0 n :=
        MaxContactCoverData.separateBoundary_succ hinv T (fun S' _ i => A i S') S n
      rw [hstep]
      exact key

private theorem isStrictPullback_of_length_eq_zero {X' X : Scheme.{u}} (g : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    IsStrictPullbackBlowupSeq g t s :=
  StrictPullbackBlowupSeq.isStrictPullback
    { comp := fun i hi =>
        eqToHom (congrArg t.schemeAt (by omega : i = 0)) ≫ t.isoZero.hom ≫ g ≫ s.isoZero.inv ≫
          eqToHom (congrArg s.schemeAt (by omega : (0 : ℕ) = i))
      comp_zero := by simp
      pullback := fun i hi => absurd hi (by omega)
      length_eq := by rw [ht, hs]
      center_eq := fun i hi => absurd hi (by omega) }

private theorem length_separateBoundaryOfFamily_zero (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) (S : MarkedIdealWithBoundary.{u}) :
    (separateBoundaryOfFamily hinv T A S 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = 0 := by
  have h0 : separateBoundaryOfFamily hinv T A S 0 = emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
    MaxContactCoverData.separateBoundary_zero hinv T (fun S' _ i => A i S') S
  have h1 : (separateBoundaryOfFamily hinv T A S 0).toBlowupSequenceData = BlowupSequenceData.empty S.scheme :=
    Eq.trans
      (congrArg
        (fun s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary => s.toBlowupSequenceData) h0)
      (emptyMarkedBlowupSequenceData_toBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  have hlen : (separateBoundaryOfFamily hinv T A S 0).length = 0 :=
    Eq.trans (congrArg (fun d : BlowupSequenceData S.scheme => d.length) h1)
      (BlowupSequenceData.empty_length S.scheme)
  exact hlen

private theorem dim_derivedTriple_le_dim (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u})
    (hV : S.IsAdmissible) (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (added : List (s.obj s.length).IdealSheafData) (nDrop : ℕ) :
    (MaxContactCoverData.derivedTriple S s hft added nDrop).krullDimSucc ≤ S.krullDimSucc := by
  have h : krullDimSucc (s.toMarkedSequenceOfBlowups.schemeAt s.length) ≤ S.krullDimSucc :=
    hstar.schemeDim_level_le S hV s.toMarkedSequenceOfBlowups s.length
      (s.le_toSequenceOfBlowups_length (le_refl s.length))
  show krullDimSucc (MaxContactCoverData.derivedTriple S s hft added nDrop).scheme ≤ S.krullDimSucc
  rw [MaxContactCoverData.derivedTriple_scheme]
  exact h

private theorem boundary_length_pullbackTriple (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}}
    (g : X' ⟶ S.scheme) : (LowerDimReductionPullback.pullbackTriple S g).boundary.length = S.boundary.length := by
  show (List.map (fun D : S.scheme.IdealSheafData => D.comap g) S.boundary).length
      = S.boundary.length
  simp

private theorem boundary_pullbackAlong_eq_map_comap (U : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (qq : Y ⟶ Spec (CommRingCat.of U.base)) (h : Y ⟶ U.scheme)
    (L : List U.scheme.IdealSheafData) (hL : U.boundary = L) :
    (U.pullbackAlong Y qq h).boundary = L.map (fun Dv => Dv.comap h) := by
  subst hL
  rfl

private theorem isAdmissible_withBoundary_of_eq (U : MarkedIdealWithBoundary.{u}) (hU : U.IsAdmissible)
    (L : List U.scheme.IdealSheafData) (hL : U.boundary = L) : (U.withBoundary L).IsAdmissible := by
  subst hL
  exact hU

private theorem length_toMarkedSequence_eq_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData)
    (b : SequenceOfBlowups X) (h : (BlowupSequenceData.ofSequenceOfBlowups b).IsMarked p I m E) (hb : b.length = 0) :
    ((BlowupSequenceData.ofSequenceOfBlowups b).toMarkedBlowupSequenceData p I m E h).length = 0 := hb

private theorem orderAt_le_mult_of_isOrderBoundedByMult (T : MarkedIdealWithBoundary.{u}) (h : T.IsOrderBoundedByMult) :
    ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) := h

private theorem isMaxContactHypersurface_derivedTriple (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (added : List (s.obj s.length).IdealSheafData) (nDrop : ℕ)
    (E : (s.obj s.length).IdealSheafData)
    (inst : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.derivedTriple S s hft added nDrop).structMap)
    (h : @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult) E) :
    @IsMaxContactHypersurface (MaxContactCoverData.derivedTriple S s hft added nDrop).base
      (MaxContactCoverData.derivedTriple S s hft added nDrop).instField
      (MaxContactCoverData.derivedTriple S s hft added nDrop).scheme
      (MaxContactCoverData.derivedTriple S s hft added nDrop).structMap inst
      (MaxContactCoverData.derivedTriple S s hft added nDrop).ideal
      (MaxContactCoverData.derivedTriple S s hft added nDrop).mult E := h

private theorem isMaxContactHypersurface_strictTransformAtLength (hstar : MaxContactCoverProperties.{u})
    (S : MarkedIdealWithBoundary.{u})
    (hV : S.IsAdmissible) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (Hs : S.scheme.IdealSheafData)
    (hH : ∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult Hs)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap)) :
    @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult)
      (MaxContactReduction.strictTransformAtLength s Hs) := by
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
  have := hft
  have h1 : IsMaxContactHypersurface S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length)
      S.mult (MaxContactReduction.iteratedStrictTransform s Hs s.length) :=
    isMaxContactHypersurface_iteratedStrictTransform hstar S hV hO Hs hH s s.length (le_refl s.length)
  rw [LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf, MaxContactReduction.strictTransformAtLength_eq]
  exact BoundarySeparationByMaxContact.isMaxContactHypersurface_balancedTunedSheaf hstar S.base
    (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult hV.one_le_mult
    (fun x => LowerDimReductionPullback.orderAt_ideal_length_le hstar S hV hO s x)
    (MaxContactReduction.iteratedStrictTransform s Hs s.length) h1

private theorem isMaxContactHypersurface_comap_lastMap (hAdm : MaxContactHypersurfaceSmoothPullback.{u})
    (hstar : MaxContactCoverProperties.{u}) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    {X' : Scheme.{u}} (g : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth g]
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : MarkedBlowupSequenceData (LowerDimReductionPullback.pullbackTriple S g).structMap (LowerDimReductionPullback.pullbackTriple S g).ideal
      (LowerDimReductionPullback.pullbackTriple S g).mult (LowerDimReductionPullback.pullbackTriple S g).boundary)
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hftS : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : AlgebraicGeometry.LocallyOfFiniteType
      (t.proj t.length ≫ (LowerDimReductionPullback.pullbackTriple S g).structMap))
    (Hs : (s.obj s.length).IdealSheafData)
    (h : @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hftS (LowerDimReductionPullback.tunedIdealAtLength S s hftS) (tuningExponent S.mult) Hs)
    (added : List (s.obj s.length).IdealSheafData) (nDrop : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS added nDrop).IsAdmissible) :
    @IsMaxContactHypersurface (LowerDimReductionPullback.pullbackTriple S g).base (LowerDimReductionPullback.pullbackTriple S g).instField
      (t.obj t.length) (t.proj t.length ≫ (LowerDimReductionPullback.pullbackTriple S g).structMap) hftT
      (LowerDimReductionPullback.tunedIdealAtLength (LowerDimReductionPullback.pullbackTriple S g) t hftT)
      (tuningExponent (LowerDimReductionPullback.pullbackTriple S g).mult) (Hs.comap D.lastMap) := by
  have := hV.charZero
  have := BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
  have := hftS
  have hsm : AlgebraicGeometry.Smooth (LowerDimReductionPullback.pullbackMapAtLength S g s t D) :=
    LowerDimReductionPullback.smooth_pullbackMapAtLength S g s t D
  have hftg : AlgebraicGeometry.LocallyOfFiniteType
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap)) := by
    rw [LowerDimReductionPullback.pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D]
    exact hftT
  have key := hAdm S.base (s.obj s.length) (s.proj s.length ≫ S.structMap) (t.obj t.length)
    (LowerDimReductionPullback.pullbackMapAtLength S g s t D) (LowerDimReductionPullback.tunedIdealAtLength S s hftS) (tuningExponent S.mult)
    (one_le_tuningExponent S.mult) Hs h
  exact @isMaxContactHypersurface_of_eq_of_eq_of_eq S.base S.instField (t.obj t.length)
    (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap))
    (t.proj t.length ≫ (LowerDimReductionPullback.pullbackTriple S g).structMap) hftg hftT
    ((LowerDimReductionPullback.tunedIdealAtLength S s hftS).comap (LowerDimReductionPullback.pullbackMapAtLength S g s t D))
    (LowerDimReductionPullback.tunedIdealAtLength (LowerDimReductionPullback.pullbackTriple S g) t hftT)
    (Hs.comap (LowerDimReductionPullback.pullbackMapAtLength S g s t D)) (Hs.comap (LowerDimReductionPullback.pullbackMapAtLength S g s t D))
    (tuningExponent S.mult)
    (LowerDimReductionPullback.pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D)
    (LowerDimReductionPullback.tunedIdealAtLength_comap_pullbackMapAtLength S g s t D hftS hftT added nDrop hVc) rfl key

private theorem isAdmissible_derivedTriple_pullbackTriple (hin : OrderReduction.OrderReductionHypotheses.{u})
    (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (g : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth g]
    [AlgebraicGeometry.Flat g] (hV' : (LowerDimReductionPullback.pullbackTriple S g).IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : MarkedBlowupSequenceData (LowerDimReductionPullback.pullbackTriple S g).structMap (LowerDimReductionPullback.pullbackTriple S g).ideal
      (LowerDimReductionPullback.pullbackTriple S g).mult (LowerDimReductionPullback.pullbackTriple S g).boundary)
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hNs : ∀ i ≤ s.length, AlgebraicGeometry.IsLocallyNoetherian (s.obj i))
    (hNt : ∀ i ≤ t.length, AlgebraicGeometry.IsLocallyNoetherian (t.obj i))
    (hftS : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : AlgebraicGeometry.LocallyOfFiniteType
      (t.proj t.length ≫ (LowerDimReductionPullback.pullbackTriple S g).structMap))
    (added : List (s.obj s.length).IdealSheafData) (nDrop : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS added nDrop).IsAdmissible) :
    (MaxContactCoverData.derivedTriple (LowerDimReductionPullback.pullbackTriple S g) t hftT
      (LowerDimReductionPullback.comapBoundaryPullback S g s t D added) nDrop).IsAdmissible := by
  have hsm : AlgebraicGeometry.Smooth (LowerDimReductionPullback.pullbackMapAtLength S g s t D) :=
    LowerDimReductionPullback.smooth_pullbackMapAtLength S g s t D
  have hlev : ((LowerDimReductionPullback.pullbackTriple S g).transformAt t.toMarkedSequenceOfBlowups t.length).IsAdmissible :=
    MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hV' t.toMarkedSequenceOfBlowups t.length
      (t.le_toSequenceOfBlowups_length (le_refl t.length))
  have hqc0 := hlev.quasiCompact
  rw [MarkedIdealWithBoundary.transformAt_structureMorphism, MarkedSequenceOfBlowups.projectionToSpec_eq,
    MarkedBlowupSequenceData.toMarkedSequence_projectionToBase] at hqc0
  have hqcA : AlgebraicGeometry.QuasiCompact
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap)) := by
    rw [LowerDimReductionPullback.pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D]
    exact hqc0
  have hpb := @OrderReduction.OrderReductionHypotheses.valid_pullbackAlong hin
    (MaxContactCoverData.derivedTriple S s hftS added nDrop) hVc (t.obj t.length)
    (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS added nDrop).structMap)
    (LowerDimReductionPullback.pullbackMapAtLength S g s t D) hsm hqcA rfl
  have hbd1 : ((MaxContactCoverData.derivedTriple S s hftS added nDrop).pullbackAlong (t.obj t.length)
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS added nDrop).structMap)
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D)).boundary
      = (added ++ (s.boundary s.length).drop nDrop).map
          (fun Dv => Dv.comap (LowerDimReductionPullback.pullbackMapAtLength S g s t D)) :=
    boundary_pullbackAlong_eq_map_comap (MaxContactCoverData.derivedTriple S s hftS added nDrop)
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS added nDrop).structMap)
      (LowerDimReductionPullback.pullbackMapAtLength S g s t D) _
      (MaxContactCoverData.derivedTriple_boundary S s hftS added nDrop)
  have hbd2 : (added ++ (s.boundary s.length).drop nDrop).map
        (fun Dv => Dv.comap (LowerDimReductionPullback.pullbackMapAtLength S g s t D))
      = LowerDimReductionPullback.comapBoundaryPullback S g s t D added ++ (t.boundary t.length).drop nDrop := by
    rw [List.map_append, List.map_drop, LowerDimReductionPullback.boundary_eq_map_comap_pullbackMapAtLength S g s t D hNs hNt]
  rw [← LowerDimReductionPullback.pullbackAlong_derivedTriple_eq S g s t D hftS hftT added nDrop hVc]
  exact isAdmissible_withBoundary_of_eq _ hpb _ (hbd1.trans hbd2)

private theorem isomorphic_appendLowerDimReduction_of_isMaxContactHypersurface (hstar : MaxContactCoverProperties.{u})
    (hin : OrderReduction.OrderReductionHypotheses.{u}) (hMC : IsMaxContactInvariantBalancedTuned.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (nDrop : ℕ) (E1 E2 : (s.obj s.length).IdealSheafData)
    (hV1 : (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).IsAdmissible)
    (hV2 : (MaxContactCoverData.derivedTriple S s hft [E2] nDrop).IsAdmissible)
    (hR1 : @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult) E1)
    (hR2 : @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ S.structMap) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult) E2)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take nDrop,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : Set ↥(s.obj s.length)) = ∅) :
    (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s [E1] nDrop
        0).toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s [E2] nDrop
        0).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  classical
  have hdim1 : (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).krullDimSucc ≤ T.krullDimSucc :=
    le_trans (dim_derivedTriple_le_dim hstar S hV s hft [E1] nDrop) hdimS
  have hdim2 : (MaxContactCoverData.derivedTriple S s hft [E2] nDrop).krullDimSucc ≤ T.krullDimSucc :=
    le_trans (dim_derivedTriple_le_dim hstar S hV s hft [E2] nDrop) hdimS
  have hj1 : 0 < ([E1] ++ (s.boundary s.length).drop nDrop).length := by simp
  have hj2 : 0 < ([E2] ++ (s.boundary s.length).drop nDrop).length := by simp
  obtain ⟨hmk1, hc1, -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B 0 (hspec 0)
    (fun S' _ i => A i S') (fun _ _ _ => rfl) S hV hV.one_le_mult hO s [E1] nDrop hft hdim1
    (hmono _ _ hdim1 hPdimT) hV1 hj1 hsep
  obtain ⟨hmk2, hc2, -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B 0 (hspec 0)
    (fun S' _ i => A i S') (fun _ _ _ => rfl) S hV hV.one_le_mult hO s [E2] nDrop hft hdim2
    (hmono _ _ hdim2 hPdimT) hV2 hj2 hsep
  rw [hc1, hc2]
  by_cases hne : (orderAtLeastLocus (s.ideal s.length) S.mult).Nonempty
  · have := hV.charZero
    have := BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length (le_refl s.length)
    have := hft
    have hmax : MaxOrderEq (s.ideal s.length) S.mult :=
      LowerDimReductionPullback.maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne
    have hbdT : (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).boundary
        = E1 :: (s.boundary s.length).drop nDrop :=
      MaxContactCoverData.derivedTriple_boundary S s hft [E1] nDrop
    have hA1 : ∀ [inst : AlgebraicGeometry.LocallyOfFiniteType
        (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap],
        IsMaxContactHypersurface (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).base
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).ideal
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).mult E1 := by
      intro inst
      exact isMaxContactHypersurface_derivedTriple S s hft [E1] nDrop E1 inst hR1
    have hA2 : ∀ [inst : AlgebraicGeometry.LocallyOfFiniteType
        (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap],
        IsMaxContactHypersurface (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).base
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).ideal
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).mult E2 := by
      intro inst
      exact isMaxContactHypersurface_derivedTriple S s hft [E1] nDrop E2 inst hR2
    have hMCinv : ∀ [inst : AlgebraicGeometry.LocallyOfFiniteType
        (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap],
        IsMaxContactInvariant (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).base
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).structMap
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).ideal
          (MaxContactCoverData.derivedTriple S s hft [E1] nDrop).mult := by
      intro inst
      rw [MaxContactCoverData.derivedTriple_mult, LowerDimReductionPullback.ideal_derivedTriple, LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf]
      exact hMC S.base (s.obj s.length) (s.proj s.length ≫ S.structMap) (s.ideal s.length)
        S.mult hV.one_le_mult hmax
    have hEq := DivisorReductionIndependence.isomorphic_withBoundary_cons_of_isMaxContactHypersurface hin P hmono (A 0) B (hspec 0)
      (MaxContactCoverData.derivedTriple S s hft [E1] nDrop) hV1 (hmono _ _ hdim1 hPdimT)
      (orderAt_le_mult_of_isOrderBoundedByMult _
        (LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hV.one_le_mult hO s hft [E1] nDrop hV1))
      (fun _ => LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hV.one_le_mult hO s hft [E1] nDrop hV1)
      hMCinv ((s.boundary s.length).drop nDrop) E1 E2 hbdT hV2 hA1 hA2
    refine MarkedBlowupSequenceData.append_isomorphic_of_isomorphic s _ _ hinv ?_
    exact SequenceOfBlowups.Isomorphic.trans
      (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic
        (A 0 (MaxContactCoverData.derivedTriple S s hft [E1] nDrop)).toSequenceOfBlowups)
      (SequenceOfBlowups.Isomorphic.trans hEq
        (SequenceOfBlowups.Isomorphic.symm
          (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic
            (A 0 (MaxContactCoverData.derivedTriple S s hft [E2] nDrop)).toSequenceOfBlowups)))
  · have hempty : orderAtLeastLocus (s.ideal s.length) S.mult = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    have hl1 : (A 0 (MaxContactCoverData.derivedTriple S s hft [E1] nDrop)).length = 0 :=
      LowerDimReductionPullback.length_eq_zero_of_orderAtLeastLocus_eq_empty hstar P 0 (A 0) B (hspec 0) S hV hV.one_le_mult hO s hft
        [E1] nDrop (hmono _ _ hdim1 hPdimT) hV1 hj1 hempty
    have hl2 : (A 0 (MaxContactCoverData.derivedTriple S s hft [E2] nDrop)).length = 0 :=
      LowerDimReductionPullback.length_eq_zero_of_orderAtLeastLocus_eq_empty hstar P 0 (A 0) B (hspec 0) S hV hV.one_le_mult hO s hft
        [E2] nDrop (hmono _ _ hdim2 hPdimT) hV2 hj2 hempty
    have e1 := MarkedBlowupSequenceData.append_isomorphic_of_length_eq_zero s _ hinv
      (length_toMarkedSequence_eq_zero (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
        (s.boundary s.length) (A 0 (MaxContactCoverData.derivedTriple S s hft [E1] nDrop)).toSequenceOfBlowups
        hmk1 hl1)
    have e2 := MarkedBlowupSequenceData.append_isomorphic_of_length_eq_zero s _ hinv
      (length_toMarkedSequence_eq_zero (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
        (s.boundary s.length) (A 0 (MaxContactCoverData.derivedTriple S s hft [E2] nDrop)).toSequenceOfBlowups
        hmk2 hl2)
    exact SequenceOfBlowups.Isomorphic.trans e1 (SequenceOfBlowups.Isomorphic.symm e2)

theorem isStrictPullbackBlowupSeq_reduceAlongHypersurface (hstar : MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hMC : IsMaxContactInvariantBalancedTuned.{u}) (hAdm : MaxContactHypersurfaceSmoothPullback.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.Flat q] [AlgebraicGeometry.Surjective q]
    (hV' : (LowerDimReductionPullback.pullbackTriple S q).IsAdmissible) (hdim' : (LowerDimReductionPullback.pullbackTriple S q).krullDimSucc ≤ T.krullDimSucc)
    (H' : (LowerDimReductionPullback.pullbackTriple S q).scheme.IdealSheafData)
    (hH' : ∀ [AlgebraicGeometry.LocallyOfFiniteType (LowerDimReductionPullback.pullbackTriple S q).structMap],
      IsMaxContactHypersurface (LowerDimReductionPullback.pullbackTriple S q).base (LowerDimReductionPullback.pullbackTriple S q).structMap
        (LowerDimReductionPullback.pullbackTriple S q).ideal (LowerDimReductionPullback.pullbackTriple S q).mult H')
    (hH'snc : InStrictNormalCrossingPosition (LowerDimReductionPullback.pullbackTriple S q).structMap [H']) :
    IsStrictPullbackBlowupSeq q
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') (LowerDimReductionPullback.pullbackTriple S q)
        H').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  classical
  have hO' := orderAt_pullbackTriple_le_mult S q hV hO
  have hLen : (LowerDimReductionPullback.pullbackTriple S q).boundary.length = S.boundary.length :=
    boundary_length_pullbackTriple S q
  have key : ∀ n : ℕ, n ≤ S.boundary.length →
      IsStrictPullbackBlowupSeq q
        (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) n).toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (separateBoundaryOfFamily hinv T A S n).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
    intro n
    induction n with
    | zero =>
        intro _
        exact isStrictPullback_of_length_eq_zero q _ _
          (length_separateBoundaryOfFamily_zero hinv T A (LowerDimReductionPullback.pullbackTriple S q))
          (length_separateBoundaryOfFamily_zero hinv T A S)
    | succ m ih =>
        intro hm
        have hm' : m < S.boundary.length := lt_of_lt_of_le (Nat.lt_succ_self m) hm
        have D := (ih (le_of_lt hm')).toStrictPullbackBlowupSeq
        have hftS := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV
          (separateBoundaryOfFamily hinv T A S m) (separateBoundaryOfFamily hinv T A S m).length le_rfl
        have hftT := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar
          (LowerDimReductionPullback.pullbackTriple S q) hV' (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m)
          (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m).length le_rfl
        have hdim : (MaxContactCoverData.derivedTriple S (separateBoundaryOfFamily hinv T A S m) hftS
            ([] : List ((separateBoundaryOfFamily hinv T A S m).obj
              (separateBoundaryOfFamily hinv T A S m).length).IdealSheafData) 0).krullDimSucc ≤ T.krullDimSucc :=
          le_trans (dim_derivedTriple_le_dim hstar S hV (separateBoundaryOfFamily hinv T A S m) hftS [] 0) hdimS
        have hdimb : (MaxContactCoverData.derivedTriple (LowerDimReductionPullback.pullbackTriple S q)
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) hftT
            ([] : List ((separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m).obj
              (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m).length).IdealSheafData)
            0).krullDimSucc ≤ T.krullDimSucc :=
          le_trans (dim_derivedTriple_le_dim hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) hftT [] 0) hdim'
        have hres := LowerDimReductionPullback.nonempty_strictPullback_appendLowerDimReduction S q (separateBoundaryOfFamily hinv T A S m)
          (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) D hstar hinv T P A B m (hspec m)
          (fun S' _ i => A i S') (fun _ _ _ => rfl) [] 0 hftS hftT hV hV.one_le_mult hO
          (isLocallyNoetherian_schemeAt hstar S hV (separateBoundaryOfFamily hinv T A S m)) hV' hO'
          (isLocallyNoetherian_schemeAt hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m))
          hdim (hmono _ _ hdim hPdimT)
          (isAdmissible_derivedTriple_nil hstar S hV (separateBoundaryOfFamily hinv T A S m) hftS)
          (lt_length_nil_append_boundary_drop_zero S (separateBoundaryOfFamily hinv T A S m) m hm')
          (orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero S (separateBoundaryOfFamily hinv T A S m))
          hdimb (hmono _ _ hdimb hPdimT)
          (isAdmissible_derivedTriple_nil hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) hftT)
          (lt_length_nil_append_boundary_drop_zero (LowerDimReductionPullback.pullbackTriple S q)
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) m (by rw [hLen]; exact hm'))
          (orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero (LowerDimReductionPullback.pullbackTriple S q)
            (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m))
        have e1 : separateBoundaryOfFamily hinv T A S (m + 1)
            = MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S
              (separateBoundaryOfFamily hinv T A S m) [] 0 m :=
          MaxContactCoverData.separateBoundary_succ hinv T (fun S' _ i => A i S') S m
        have e2 : separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) (m + 1)
            = MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') (LowerDimReductionPullback.pullbackTriple S q)
              (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) m) [] 0 m :=
          MaxContactCoverData.separateBoundary_succ hinv T (fun S' _ i => A i S') (LowerDimReductionPullback.pullbackTriple S q) m
        rw [e1, e2]
        exact hres.elim fun D' => D'.isStrictPullback
  have hftS2 := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV
    (separateBoundaryOfFamily hinv T A S S.boundary.length)
    (separateBoundaryOfFamily hinv T A S S.boundary.length).length le_rfl
  have hftT2 := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length)
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length).length le_rfl
  have hTS := separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T hPdimT S hV hO
    hdimS H hHsnc S.boundary.length le_rfl
  have hTS' := separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T hPdimT
    (LowerDimReductionPullback.pullbackTriple S q) hV' hO' hdim' H' hH'snc (LowerDimReductionPullback.pullbackTriple S q).boundary.length le_rfl
  rw [hLen] at hTS'
  have hsncF0 := inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar S hV hO H
    (@hH hV.locallyOfFiniteType) (separateBoundaryOfFamily hinv T A S S.boundary.length) hTS.2.2
    (separateBoundaryOfFamily hinv T A S S.boundary.length).length le_rfl
  rw [← MaxContactReduction.strictTransformAtLength_eq] at hsncF0
  have hVcF := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV
    (separateBoundaryOfFamily hinv T A S S.boundary.length) hftS2
    [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
    S.boundary.length hsncF0
  have hsncF0' := inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar (LowerDimReductionPullback.pullbackTriple S q) hV' hO' H'
    (@hH' hV'.locallyOfFiniteType)
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hTS'.2.2
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length).length le_rfl
  rw [← MaxContactReduction.strictTransformAtLength_eq, hLen] at hsncF0'
  have hVcF' := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hftT2
    [MaxContactReduction.strictTransformAtLength
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) H']
    S.boundary.length hsncF0'
  rw [MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction, MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction, hLen]
  have D := (key S.boundary.length le_rfl).toStrictPullbackBlowupSeq
  have hdimF : (MaxContactCoverData.derivedTriple S (separateBoundaryOfFamily hinv T A S S.boundary.length) hftS2
      [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length).krullDimSucc ≤ T.krullDimSucc :=
    le_trans (dim_derivedTriple_le_dim hstar S hV (separateBoundaryOfFamily hinv T A S S.boundary.length) hftS2
      [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length) hdimS
  have hVcF2 := isAdmissible_derivedTriple_pullbackTriple hin S q hV'
    (separateBoundaryOfFamily hinv T A S S.boundary.length)
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) D
    (isLocallyNoetherian_schemeAt hstar S hV (separateBoundaryOfFamily hinv T A S S.boundary.length))
    (isLocallyNoetherian_schemeAt hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length))
    hftS2 hftT2
    [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
    S.boundary.length hVcF
  have hdimF' : (MaxContactCoverData.derivedTriple (LowerDimReductionPullback.pullbackTriple S q)
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hftT2
      (LowerDimReductionPullback.comapBoundaryPullback S q (separateBoundaryOfFamily hinv T A S S.boundary.length)
        (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) D
        [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H])
      S.boundary.length).krullDimSucc ≤ T.krullDimSucc :=
    le_trans (dim_derivedTriple_le_dim hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hftT2 _
      S.boundary.length) hdim'
  have hNonempty := LowerDimReductionPullback.nonempty_strictPullback_appendLowerDimReduction S q
      (separateBoundaryOfFamily hinv T A S S.boundary.length)
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) D hstar hinv T P A B 0
      (hspec 0) (fun S' _ i => A i S') (fun _ _ _ => rfl)
      [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length
      hftS2 hftT2 hV hV.one_le_mult hO
      (isLocallyNoetherian_schemeAt hstar S hV (separateBoundaryOfFamily hinv T A S S.boundary.length)) hV' hO'
      (isLocallyNoetherian_schemeAt hstar (LowerDimReductionPullback.pullbackTriple S q) hV'
        (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length))
      hdimF (hmono _ _ hdimF hPdimT) hVcF (by simp)
      (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated S (separateBoundaryOfFamily hinv T A S S.boundary.length) S.boundary.length hTS.1)
      hdimF' (hmono _ _ hdimF' hPdimT) hVcF2 (by simp)
      (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated (LowerDimReductionPullback.pullbackTriple S q)
        (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) S.boundary.length
        hTS'.1)
  have hMaxContactS := isMaxContactHypersurface_strictTransformAtLength hstar S hV hO H hH
    (separateBoundaryOfFamily hinv T A S S.boundary.length) hftS2
  have hMaxContactT := isMaxContactHypersurface_strictTransformAtLength hstar (LowerDimReductionPullback.pullbackTriple S q) hV' hO' H' hH'
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hftT2
  have hMaxContactComap := isMaxContactHypersurface_comap_lastMap hAdm hstar S hV q
    (separateBoundaryOfFamily hinv T A S S.boundary.length)
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) D hftS2 hftT2
    (MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H) hMaxContactS
    [MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H]
    S.boundary.length hVcF
  have he := isomorphic_appendLowerDimReduction_of_isMaxContactHypersurface hstar hin hMC hinv P hmono A B hspec T hPdimT
    (LowerDimReductionPullback.pullbackTriple S q) hV' hO' hdim'
    (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) hftT2 S.boundary.length
    ((MaxContactReduction.strictTransformAtLength (separateBoundaryOfFamily hinv T A S S.boundary.length) H).comap D.lastMap)
    (MaxContactReduction.strictTransformAtLength
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) H')
    hVcF2 hVcF' hMaxContactComap hMaxContactT
    (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated (LowerDimReductionPullback.pullbackTriple S q)
      (separateBoundaryOfFamily hinv T A (LowerDimReductionPullback.pullbackTriple S q) S.boundary.length) S.boundary.length hTS'.1)
  exact hNonempty.elim fun D' => IsStrictPullbackBlowupSeq.of_isomorphic_pullback D'.isStrictPullback he

end BoundarySeparationBaseChange

end FunctorialResolution.EmbeddedResolution

end
