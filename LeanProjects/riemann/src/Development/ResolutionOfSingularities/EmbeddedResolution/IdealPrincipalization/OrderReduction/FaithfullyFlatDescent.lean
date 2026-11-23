import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMapSurjective
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem IsStrictPullbackBlowupSeq.congr_hom {X' X : Scheme.{u}} {g g' : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq g t s) (hg : g = g') :
    IsStrictPullbackBlowupSeq g' t s := by
  subst hg
  exact h

theorem IsStrictPullbackBlowupSeq.congr_sourceSeq {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t t' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq g t s) (ht : t = t') :
    IsStrictPullbackBlowupSeq g t' s := by
  subst ht
  exact h

theorem IsStrictPullbackBlowupSeq.baseChange_of_comp {Q Y X : Scheme.{u}} {φ : Q ⟶ Y} {h : Y ⟶ X}
    [AlgebraicGeometry.Flat φ] [AlgebraicGeometry.Flat h]
    {u : SequenceOfBlowups Q} {s : SequenceOfBlowups X}
    (hu : IsStrictPullbackBlowupSeq (φ ≫ h) u s) :
    IsStrictPullbackBlowupSeq φ u (s.baseChange h) := by
  have ht : IsStrictPullbackBlowupSeq h (s.baseChange h) s :=
    isStrictPullbackSequenceOfBlowups_baseChange s h
  have hw : IsStrictPullbackBlowupSeq φ ((s.baseChange h).baseChange φ) (s.baseChange h) :=
    isStrictPullbackSequenceOfBlowups_baseChange (s.baseChange h) φ
  have hwc : IsStrictPullbackBlowupSeq (φ ≫ h) ((s.baseChange h).baseChange φ) s := hw.comp ht
  exact hw.of_isomorphic_pullback (hwc.isomorphic hu)

theorem comap_ne_top_iff_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.Surjective f] (J : Y.IdealSheafData) :
    J.comap f ≠ ⊤ ↔ J ≠ ⊤ := by
  have hsurj : Function.Surjective f.base := AlgebraicGeometry.Surjective.surj
  have htop : (⊤ : Y.IdealSheafData).comap f = ⊤ := by simp
  have hpre : ((J.comap f).support : Set ↥X) = f.base ⁻¹' ((J.support : Set ↥Y)) := by simp
  have hbot : J.support = ⊥ → J = ⊤ := by simp
  constructor
  · intro h hJ
    apply h
    rw [hJ, htop]
  · intro hJ h
    apply hJ
    apply hbot
    apply SetLike.ext'
    have hsupp : ((J.support : Set ↥Y)) = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hsurj y
      have hx : x ∈ ((J.comap f).support : Set ↥X) := by
        rw [hpre]
        exact Set.mem_preimage.mpr hy
      rw [h] at hx
      simp at hx
    simpa using hsupp

namespace MaxContactFunctoriality

theorem isMaxContactHypersurface_of_triple_eq {T₁ T₂ : MarkedIdealWithBoundary.{u}} (hT : T₁ = T₂)
    (hft₁ : AlgebraicGeometry.LocallyOfFiniteType T₁.structMap)
    (hft₂ : AlgebraicGeometry.LocallyOfFiniteType T₂.structMap)
    (H₁ : T₁.scheme.IdealSheafData) (H₂ : T₂.scheme.IdealSheafData) (hH : HEq H₁ H₂)
    (h : haveI := hft₂;
      IsMaxContactHypersurface T₂.base T₂.structMap T₂.ideal T₂.mult H₂) :
    haveI := hft₁;
      IsMaxContactHypersurface T₁.base T₁.structMap T₁.ideal T₁.mult H₁ := by
  subst hT
  have hHe : H₁ = H₂ := eq_of_heq hH
  subst hHe
  exact h

theorem inStrictNormalCrossingPosition_of_triple_eq {T₁ T₂ : MarkedIdealWithBoundary.{u}} (hT : T₁ = T₂)
    (L₁ : List T₁.scheme.IdealSheafData) (L₂ : List T₂.scheme.IdealSheafData) (hL : HEq L₁ L₂)
    (h : InStrictNormalCrossingPosition T₂.structMap L₂) :
    InStrictNormalCrossingPosition T₁.structMap L₁ := by
  subst hT
  have hLe : L₁ = L₂ := eq_of_heq hL
  subst hLe
  exact h

theorem orderAtLeastLocus_comap_eq_empty (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) {Y : Scheme.{u}}
    (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h]
    (hemp : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    orderAtLeastLocus (T.ideal.comap h) T.mult = (∅ : Set ↥Y) := by
  have hcz : CharZero T.base := by
    cases hv
    assumption
  have hsm : AlgebraicGeometry.Smooth T.structMap := by
    cases hv
    assumption
  rw [orderAtLeastLocus_comap T.base T.structMap h T.ideal T.mult, hemp, Set.preimage_empty]

private theorem derivedTriple_dim_le (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) :
    (MaxContactCoverData.derivedTriple S s hft extra keep).krullDimSucc ≤ S.krullDimSucc :=
  hstar.schemeDim_level_le S hV s.toMarkedSequenceOfBlowups s.length le_rfl

private theorem appendLowerDimReduction_congr_of_dim_le (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
    (hinv : ComapIsoInvariance.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) (T₁ T₂ : MarkedIdealWithBoundary.{u}) (hdim : T₁.krullDimSucc ≤ T₂.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hS : S.krullDimSucc ≤ T₁.krullDimSucc)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep n : ℕ) :
    MaxContactReduction.appendLowerDimReduction hinv T₁ (lowerDimensionalFamily A T₁) S s extra keep n =
      MaxContactReduction.appendLowerDimReduction hinv T₂ (lowerDimensionalFamily A T₂) S s extra keep n := by
  by_cases hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap)
  · have h1 : (MaxContactCoverData.derivedTriple S s hft extra keep).krullDimSucc ≤ T₁.krullDimSucc :=
      le_trans (derivedTriple_dim_le hstar S hV s hft extra keep) hS
    exact (MaxContactCoverData.appendLowerDimReduction_eq_concatOfIsMarked hinv T₁ (lowerDimensionalFamily A T₁) S s extra keep n
        hft h1).trans
      (MaxContactCoverData.appendLowerDimReduction_eq_concatOfIsMarked hinv T₂ (lowerDimensionalFamily A T₂) S s extra keep n
        hft (le_trans h1 hdim)).symm
  · exact (MaxContactCoverData.appendLowerDimReduction_of_not_locallyOfFiniteType hinv T₁ (lowerDimensionalFamily A T₁) S s extra
        keep n hft).trans
      (MaxContactCoverData.appendLowerDimReduction_of_not_locallyOfFiniteType hinv T₂ (lowerDimensionalFamily A T₂) S s extra
        keep n hft).symm

private theorem separateBoundary_congr_of_dim_le (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
    (hinv : ComapIsoInvariance.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) (T₁ T₂ : MarkedIdealWithBoundary.{u}) (hdim : T₁.krullDimSucc ≤ T₂.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hS : S.krullDimSucc ≤ T₁.krullDimSucc) (j : ℕ) :
    MaxContactReduction.separateBoundary hinv T₁ (lowerDimensionalFamily A T₁) S j =
      MaxContactReduction.separateBoundary hinv T₂ (lowerDimensionalFamily A T₂) S j := by
  induction j with
  | zero =>
    rw [MaxContactCoverData.separateBoundary_zero hinv T₁ (lowerDimensionalFamily A T₁) S,
      MaxContactCoverData.separateBoundary_zero hinv T₂ (lowerDimensionalFamily A T₂) S]
  | succ n ih =>
    rw [MaxContactCoverData.separateBoundary_succ hinv T₁ (lowerDimensionalFamily A T₁) S n,
      MaxContactCoverData.separateBoundary_succ hinv T₂ (lowerDimensionalFamily A T₂) S n, ih]
    exact appendLowerDimReduction_congr_of_dim_le hstar hinv A T₁ T₂ hdim S hV hS
      (MaxContactReduction.separateBoundary hinv T₂ (lowerDimensionalFamily A T₂) S n) [] 0 n

theorem reduceAlongHypersurface_congr_of_dim_le (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
    (hinv : ComapIsoInvariance.{u})
    (A : ℕ → PrincipalizationAssignment.{u}) (T₁ T₂ : MarkedIdealWithBoundary.{u}) (hdim : T₁.krullDimSucc ≤ T₂.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hS : S.krullDimSucc ≤ T₁.krullDimSucc)
    (H : S.scheme.IdealSheafData) :
    MaxContactReduction.reduceAlongHypersurface hinv T₁ (lowerDimensionalFamily A T₁) S H =
      MaxContactReduction.reduceAlongHypersurface hinv T₂ (lowerDimensionalFamily A T₂) S H := by
  rw [MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction hinv T₁ (lowerDimensionalFamily A T₁) S H,
    MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction hinv T₂ (lowerDimensionalFamily A T₂) S H,
    separateBoundary_congr_of_dim_le hstar hinv A T₁ T₂ hdim S hV hS S.boundary.length]
  exact appendLowerDimReduction_congr_of_dim_le hstar hinv A T₁ T₂ hdim S hV hS _ _ S.boundary.length 0

theorem reduceAlongHypersurface_toSequenceOfBlowups_heq (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (resolveLower : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups)
    {S₁ S₂ : MarkedIdealWithBoundary.{u}} (hS : S₁ = S₂)
    (H₁ : S₁.scheme.IdealSheafData) (H₂ : S₂.scheme.IdealSheafData) (hH : HEq H₁ H₂) :
    HEq (MaxContactReduction.reduceAlongHypersurface hinv T resolveLower S₁ H₁).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T resolveLower S₂ H₂).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  subst hS
  have hHe : H₁ = H₂ := eq_of_heq hH
  subst hHe
  exact HEq.refl _

def MarkingDescends (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme),
    IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toSequenceOfBlowups d.toSequenceOfBlowups →
      d.IsMarked T.structMap T.ideal T.mult T.boundary

def CoverFaithfullyFlat (P : ℕ → Prop) : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T),
    AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap T h.valid) ∧
      AlgebraicGeometry.Flat (MaxContactCoverData.coverMap T h.valid)

def DropTrivialBoundaryAdmissible : Prop :=
  ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → (MaxContactReduction.dropTrivialBoundary T).IsAdmissible

def MarkedOfMarkedDropTrivialBoundary : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ d : BlowupSequenceData T.scheme,
    d.IsMarked T.structMap T.ideal T.mult (MaxContactReduction.dropTrivialBoundary T).boundary →
      d.IsMarked T.structMap T.ideal T.mult T.boundary

theorem OrderReductionHypotheses.of_dropTrivialBoundaryAdmissible {P : ℕ → Prop} {T : MarkedIdealWithBoundary.{u}} (h : OrderReductionHypotheses P T)
    (htv : DropTrivialBoundaryAdmissible.{u}) : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := by
  refine ⟨?_, ?_, ?_, htv T h.valid⟩
  · exact h.dim_prop
  · exact h.orderLE
  · exact h.coSupport_nonempty

theorem exists_isStrictPullback_cover_dropTrivialBoundary {hinv : ComapIsoInvariance.{u}} {P : ℕ → Prop}
    {A : ℕ → PrincipalizationAssignment.{u}} (hstar : CoverSequenceProperties hinv P A)
    (hdesc : MarkingDescends hinv P A) (htv : DropTrivialBoundaryAdmissible.{u}) (htm : MarkedOfMarkedDropTrivialBoundary.{u})
    (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) :
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid)
          (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid hinv
            (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toSequenceOfBlowups d.toSequenceOfBlowups ∧
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups = d.toSequenceOfBlowups := by
  obtain ⟨d0, hd0⟩ := hstar.descends (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv)
  obtain ⟨d, hdsome⟩ :=
    MaxContactCoverData.exists_descendStrictPullback_eq_some
      (T := MaxContactReduction.dropTrivialBoundary T)
      (S := MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid)
      (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid)
      (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid hinv
        (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T)))
      ⟨d0, hd0⟩
  have hpb : IsStrictPullbackBlowupSeq
      (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid)
      (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid hinv
        (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toSequenceOfBlowups d.toSequenceOfBlowups :=
    MaxContactCoverData.isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some _ _ hdsome
  have hm0 : d.IsMarked (MaxContactReduction.dropTrivialBoundary T).structMap (MaxContactReduction.dropTrivialBoundary T).ideal
      (MaxContactReduction.dropTrivialBoundary T).mult (MaxContactReduction.dropTrivialBoundary T).boundary :=
    hdesc (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv) d hpb
  have hm : d.IsMarked T.structMap T.ideal T.mult T.boundary := htm T h.valid d hm0
  refine ⟨d, hpb, ?_⟩
  rw [maxContactPrincipalization_apply,
    MaxContactCoverData.reduceOrder_eq_asMarkedSeq hinv T (lowerDimensionalFamily A T) h.valid h.orderAtLeastLocus_ne_empty
      (h.of_dropTrivialBoundaryAdmissible htv).valid d hdsome]
  exact MaxContactCoverData.asMarkedSeq_toSequenceOfBlowups T d hm

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution

end
