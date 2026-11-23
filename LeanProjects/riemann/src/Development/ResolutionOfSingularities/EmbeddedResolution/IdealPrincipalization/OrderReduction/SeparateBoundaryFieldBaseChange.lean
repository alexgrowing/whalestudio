import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusAfterReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationPullbackComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def IsBaseChangeInherited (P : ℕ → Prop) : Prop :=
  ∀ (R : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] [CharZero L] (f : R.base →+* L),
    R.IsAdmissible → P R.krullDimSucc →
    (∀ x : ↥R.scheme, orderAt R.ideal x ≤ (R.mult : ℕ∞)) →
    (∀ hft : AlgebraicGeometry.LocallyOfFiniteType R.structMap, R.IsBalanced hft) →
      (R.baseChange L f).IsAdmissible ∧
      P (R.baseChange L f).krullDimSucc ∧
      (∀ x : ↥(R.baseChange L f).scheme,
        orderAt (R.baseChange L f).ideal x ≤ (R.mult : ℕ∞)) ∧
      (∀ hft : AlgebraicGeometry.LocallyOfFiniteType (R.baseChange L f).structMap,
        (R.baseChange L f).IsBalanced hft)

theorem MarkedIdealWithBoundary.length_boundary_baseChange (S : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L]
    (f : S.base →+* L) :
    (S.baseChange L f).boundary.length = S.boundary.length := by
  have h : (S.baseChange L f).boundary.length
      = (List.map (fun D => D.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f)))
          S.boundary).length :=
    congrArg List.length (S.baseChange_boundary L f)
  rw [h]
  simp

namespace BoundaryLoopFieldBaseChange

private theorem lt_length_nil_append_boundary (S : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (j : ℕ)
    (hj : j < S.boundary.length) :
    j < (([] : List (s.obj s.length).IdealSheafData) ++ (s.boundary s.length).drop 0).length := by
  have h : (s.boundary s.length).length = S.boundary.length + s.length :=
    s.boundary_length s.length le_rfl
  have h2 : (([] : List (s.obj s.length).IdealSheafData) ++ (s.boundary s.length).drop 0).length
      = S.boundary.length + s.length := by
    simp [h]
  rw [h2]
  omega

private theorem nonempty_strictPullback_of_length_eq_zero {X' X : Scheme.{u}} (g : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    Nonempty (StrictPullbackBlowupSeq g t s) :=
  ⟨{ comp := fun i hi =>
        eqToHom (congrArg t.schemeAt (show i = 0 by omega)) ≫ t.isoZero.hom ≫ g ≫ s.isoZero.inv ≫
          eqToHom (congrArg s.schemeAt (show (0 : ℕ) = i by omega))
     comp_zero := by simp
     pullback := fun i hi => absurd hi (by omega)
     length_eq := by rw [ht, hs]
     center_eq := fun i hi => absurd hi (by omega) }⟩

private theorem length_eq_of_strictPullbackBlowupSeq
    {k k' : Type u} [Field k] [Field k'] {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} {g : X' ⟶ X}
    (s : MarkedBlowupSequenceData p I m E) (t : MarkedBlowupSequenceData p' I' m' E')
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    t.length = s.length := by
  have h := D.length_eq
  rwa [MarkedBlowupSequenceData.toMarkedSequence_length, MarkedBlowupSequenceData.toMarkedSequence_length] at h

private def strictPullbackMapAt
    {k k' : Type u} [Field k] [Field k'] {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} {g : X' ⟶ X}
    (s : MarkedBlowupSequenceData p I m E) (t : MarkedBlowupSequenceData p' I' m' E')
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ t.length) : t.obj i ⟶ s.obj i :=
  D.comp i (t.le_toSequenceOfBlowups_length hi)

private theorem strictPullbackMapAt_zero_comp_isoObjZero_hom
    {k k' : Type u} [Field k] [Field k'] {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} {g : X' ⟶ X}
    (s : MarkedBlowupSequenceData p I m E) (t : MarkedBlowupSequenceData p' I' m' E')
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (h0 : 0 ≤ t.length) :
    strictPullbackMapAt s t D 0 h0 ≫ s.isoZero.hom = t.isoZero.hom ≫ g :=
  D.comp_zero

private theorem iteratedStrictTransform_comap_eqToHom {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (H : X.IdealSheafData) (a b : ℕ) (hab : a = b)
    (hh : s.obj a = s.obj b) :
    (MaxContactReduction.iteratedStrictTransform s H b).comap (eqToHom hh) = MaxContactReduction.iteratedStrictTransform s H a := by
  subst hab
  simp

private theorem iteratedStrictTransform_comap
    {k k' : Type u} [Field k] [Field k'] {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} {g : X' ⟶ X}
    (hflat : AlgebraicGeometry.Flat g)
    (s : MarkedBlowupSequenceData p I m E) (t : MarkedBlowupSequenceData p' I' m' E')
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hNs : ∀ i ≤ s.length, AlgebraicGeometry.IsLocallyNoetherian (s.obj i))
    (hNt : ∀ i ≤ t.length, AlgebraicGeometry.IsLocallyNoetherian (t.obj i))
    (H : X.IdealSheafData) :
    ∀ (i : ℕ) (hi : i ≤ t.length),
      MaxContactReduction.iteratedStrictTransform t (H.comap g) i
        = (MaxContactReduction.iteratedStrictTransform s H i).comap (strictPullbackMapAt s t D i hi) := by
  have := hflat
  have hlen := length_eq_of_strictPullbackBlowupSeq s t D
  intro i
  induction i with
  | zero =>
    intro hi
    rw [MaxContactReduction.iteratedStrictTransform_zero, MaxContactReduction.iteratedStrictTransform_zero,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      strictPullbackMapAt_zero_comp_isoObjZero_hom s t D hi]
  | succ i ih =>
    intro hi
    have hlt : i < t.length := hi
    have hle : i ≤ t.length := le_of_lt hlt
    have := hNs (i + 1) (by omega)
    have := hNt (i + 1) (by omega)
    have hflati : AlgebraicGeometry.Flat (strictPullbackMapAt s t D i hle) :=
      D.flat_map i (t.le_toSequenceOfBlowups_length hle)
    have := hflati
    have hsq : IsPullback (strictPullbackMapAt s t D (i + 1) hi) (t.map i) (s.map i)
        (strictPullbackMapAt s t D i hle) := by
      have h := D.pullback i (t.lt_toSequenceOfBlowups_length hlt)
      have key : ∀ (a : t.obj (i + 1) ⟶ t.obj i) (b : s.obj (i + 1) ⟶ s.obj i),
          a = t.map i → b = s.map i →
          IsPullback (strictPullbackMapAt s t D (i + 1) hi) a b (strictPullbackMapAt s t D i hle) →
          IsPullback (strictPullbackMapAt s t D (i + 1) hi) (t.map i) (s.map i) (strictPullbackMapAt s t D i hle) := by
        rintro a b rfl rfl hh
        exact hh
      exact key _ _ (MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism t i)
        (MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism s i) h
    have hc : t.center i = (s.center i).comap (strictPullbackMapAt s t D i hle) := by
      have h := D.center_eq i (t.lt_toSequenceOfBlowups_length hlt)
      have key : ∀ (a : (t.obj i).IdealSheafData) (b : (s.obj i).IdealSheafData),
          a = t.center i → b = s.center i →
          a = b.comap (strictPullbackMapAt s t D i hle) →
          t.center i = (s.center i).comap (strictPullbackMapAt s t D i hle) := by
        rintro a b rfl rfl hh
        exact hh
      exact key _ _ (MarkedBlowupSequenceData.toMarkedSequence_center t i)
        (MarkedBlowupSequenceData.toMarkedSequence_center s i) h
    have key := comap_strictTransform_of_flat_of_isLocallyNoetherian (s.map i)
      (strictPullbackMapAt s t D i hle) (t.map i) (strictPullbackMapAt s t D (i + 1) hi) hsq (s.center i)
      (MaxContactReduction.iteratedStrictTransform s H i) (s.isBlowup i (by omega))
    rw [MaxContactReduction.iteratedStrictTransform_succ, MaxContactReduction.iteratedStrictTransform_succ, key, ih hle, hc]

private theorem strictTransformAtLength_comap
    {k k' : Type u} [Field k] [Field k'] {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} {g : X' ⟶ X}
    (hflat : AlgebraicGeometry.Flat g)
    (s : MarkedBlowupSequenceData p I m E) (t : MarkedBlowupSequenceData p' I' m' E')
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hNs : ∀ i ≤ s.length, AlgebraicGeometry.IsLocallyNoetherian (s.obj i))
    (hNt : ∀ i ≤ t.length, AlgebraicGeometry.IsLocallyNoetherian (t.obj i))
    (H : X.IdealSheafData)
    (fLast : t.obj t.length ⟶ s.obj s.length)
    (hfLast : fLast = strictPullbackMapAt s t D t.length le_rfl
      ≫ eqToHom (congrArg s.obj (length_eq_of_strictPullbackBlowupSeq s t D))) :
    MaxContactReduction.strictTransformAtLength t (H.comap g)
      = (MaxContactReduction.strictTransformAtLength s H).comap fLast := by
  have h1 := iteratedStrictTransform_comap hflat s t D hNs hNt H t.length le_rfl
  rw [MaxContactReduction.strictTransformAtLength_eq, MaxContactReduction.strictTransformAtLength_eq, hfLast,
    Scheme.IdealSheafData.comap_comp,
    iteratedStrictTransform_comap_eqToHom s H t.length s.length (length_eq_of_strictPullbackBlowupSeq s t D)
      (congrArg s.obj (length_eq_of_strictPullbackBlowupSeq s t D))]
  exact h1

private theorem nonempty_strictPullbackBlowupSeq_appendLowerDimReduction
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u}) (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T T' : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (hPdimOther : P T'.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (L : Type u) [Field L] [CharZero L] (f : S.base →+* L)
    [AlgebraicGeometry.Flat (pullback.fst S.structMap (specMapOfFieldHom S.base L f))]
    (hV' : (S.baseChange L f).IsAdmissible)
    (hO' : ∀ x : ↥(S.baseChange L f).scheme,
      orderAt (S.baseChange L f).ideal x ≤ ((S.baseChange L f).mult : ℕ∞))
    (hdimS' : (S.baseChange L f).krullDimSucc ≤ T'.krullDimSucc)
    (hbc : IsBaseChangeInherited.{u} P)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : MarkedBlowupSequenceData (S.baseChange L f).structMap (S.baseChange L f).ideal
      (S.baseChange L f).mult (S.baseChange L f).boundary)
    (hftS : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : AlgebraicGeometry.LocallyOfFiniteType
      (t.proj t.length ≫ (S.baseChange L f).structMap))
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (extra : List (s.obj s.length).IdealSheafData)
    (extra' : List (t.obj t.length).IdealSheafData)
    (hextra' : extra' = extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap)
    (keep j : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsAdmissible)
    (hVc' : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D extra) keep).IsAdmissible)
    (hj : j < (extra ++ (s.boundary s.length).drop keep).length)
    (hj' : j < (@List.append (t.obj t.length).IdealSheafData (LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D extra)
      ((t.boundary t.length).drop keep)).length)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take keep,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : Set ↥(s.obj s.length)) = ∅)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take keep,
      orderAtLeastLocus (t.ideal t.length) (S.baseChange L f).mult ∩
        (Dv.support : Set ↥(t.obj t.length)) = ∅) :
    Nonempty (StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      (MaxContactReduction.appendLowerDimReduction hinv T' (fun S' _ i => A i S') (S.baseChange L f) t extra'
        keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s extra keep
        j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  subst hextra'
  have hm : 1 ≤ S.mult := hV.one_le_mult
  have hdim := hstar.derivedTriple_dim_le hV s hftS extra keep hdimS
  have hdim2 := hstar.derivedTriple_dim_le hV' t hftT (LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D extra) keep hdimS'
  have hP := hmono _ _ hdim hPdimT
  have hP2 := hmono _ _ hdim2 hPdimOther
  have hOb0 : ∀ x : ↥(MaxContactCoverData.derivedTriple S s hftS extra keep).scheme,
      orderAt (MaxContactCoverData.derivedTriple S s hftS extra keep).ideal x
        ≤ ((MaxContactCoverData.derivedTriple S s hftS extra keep).mult : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mp
      (LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS extra keep hVc)
  have hDb0 : ∀ hft : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap,
      (MaxContactCoverData.derivedTriple S s hftS extra keep).IsBalanced hft :=
    fun _ => LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  obtain ⟨hVb, hPb, hOb, hDb⟩ :=
    hbc (MaxContactCoverData.derivedTriple S s hftS extra keep) L f hVc hP hOb0 hDb0
  exact LowerDimReductionPullback.nonempty_strictPullbackSeq_appendLowerDimReduction_baseChange S L f s t D hderiv hstar hinv P A B j
    (hspec j) T T' extra keep hftS hftT hV hm hO
    (BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar S hV s) hV' hO'
    (BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar (S.baseChange L f) hV' t) hdim hP hVc hj hsep
    hdim2 hP2 hVc' hj' hsep' hVb hPb hOb hDb

private theorem nonempty_strictPullbackBlowupSeq_separateBoundary
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u}) (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T T' : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (hPdimOther : P T'.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (L : Type u) [Field L] [CharZero L] (f : S.base →+* L)
    [AlgebraicGeometry.Flat (pullback.fst S.structMap (specMapOfFieldHom S.base L f))]
    (hV' : (S.baseChange L f).IsAdmissible)
    (hO' : ∀ x : ↥(S.baseChange L f).scheme,
      orderAt (S.baseChange L f).ideal x ≤ ((S.baseChange L f).mult : ℕ∞))
    (hdimS' : (S.baseChange L f).krullDimSucc ≤ T'.krullDimSucc)
    (hbc : IsBaseChangeInherited.{u} P) :
    ∀ j : ℕ, j ≤ S.boundary.length →
      Nonempty (StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
        (MaxContactReduction.separateBoundary hinv T' (fun S' _ i => A i S')
          (S.baseChange L f) j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (MaxContactReduction.separateBoundary hinv T (fun S' _ i => A i S') S
          j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MaxContactCoverData.separateBoundary_zero, MaxContactCoverData.separateBoundary_zero]
    exact nonempty_strictPullback_of_length_eq_zero _ _ _
      (emptyMarkedBlowupSequenceData_toMarkedSequence_length _ _ _ _) (emptyMarkedBlowupSequenceData_toMarkedSequence_length _ _ _ _)
  | succ j ih =>
    intro hj
    obtain ⟨D⟩ := ih (by omega)
    rw [MaxContactCoverData.separateBoundary_succ, MaxContactCoverData.separateBoundary_succ]
    have hftS := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV
      (MaxContactReduction.separateBoundary hinv T (fun S' _ i => A i S') S j) _ le_rfl
    have hftT := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (S.baseChange L f) hV'
      (MaxContactReduction.separateBoundary hinv T' (fun S' _ i => A i S') (S.baseChange L f) j) _ le_rfl
    exact nonempty_strictPullbackBlowupSeq_appendLowerDimReduction hderiv hstar hinv P hmono A B hspec T T' hPdimT hPdimOther S
      hV hO hdimS L f hV' hO' hdimS' hbc _ _ hftS hftT D [] [] rfl 0 j
      (BoundarySeparationBaseChange.isAdmissible_derivedTriple_nil hstar S hV _ hftS)
      (BoundarySeparationBaseChange.isAdmissible_derivedTriple_nil hstar (S.baseChange L f) hV' _ hftT)
      (lt_length_nil_append_boundary S _ j (by omega))
      (lt_length_nil_append_boundary (S.baseChange L f) _ j
        (by rw [MarkedIdealWithBoundary.length_boundary_baseChange]; omega))
      (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero S _) (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero (S.baseChange L f) _)

private theorem isStrictPullbackBlowupSeq_appendLowerDimReduction_baseChange
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u}) (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T T' : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (hPdimOther : P T'.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (L : Type u) [Field L] [CharZero L] (f : S.base →+* L)
    [AlgebraicGeometry.Flat (pullback.fst S.structMap (specMapOfFieldHom S.base L f))]
    (hV' : (S.baseChange L f).IsAdmissible)
    (hO' : ∀ x : ↥(S.baseChange L f).scheme,
      orderAt (S.baseChange L f).ideal x ≤ ((S.baseChange L f).mult : ℕ∞))
    (hdimS' : (S.baseChange L f).krullDimSucc ≤ T'.krullDimSucc)
    (hbc : IsBaseChangeInherited.{u} P)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    (hH' : ∀ [AlgebraicGeometry.LocallyOfFiniteType (S.baseChange L f).structMap],
      IsMaxContactHypersurface (S.baseChange L f).base (S.baseChange L f).structMap
        (S.baseChange L f).ideal (S.baseChange L f).mult
        (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))))
    (hH'snc : InStrictNormalCrossingPosition (S.baseChange L f).structMap
      [H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))])
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (t : MarkedBlowupSequenceData (S.baseChange L f).structMap (S.baseChange L f).ideal
      (S.baseChange L f).mult (S.baseChange L f).boundary)
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take S.boundary.length,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : Set ↥(s.obj s.length)) = ∅)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take S.boundary.length,
      orderAtLeastLocus (t.ideal t.length) (S.baseChange L f).mult ∩
        (Dv.support : Set ↥(t.obj t.length)) = ∅) :
    IsStrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      (MaxContactReduction.appendLowerDimReduction hinv T' (fun S' _ i => A i S') (S.baseChange L f) t
        [MaxContactReduction.strictTransformAtLength t
          (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f)))]
        S.boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s
        [MaxContactReduction.strictTransformAtLength s H] S.boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have := hV.locallyOfFiniteType
  have := hV'.locallyOfFiniteType
  have hlen : (S.baseChange L f).boundary.length = S.boundary.length :=
    MarkedIdealWithBoundary.length_boundary_baseChange S L f
  have hftS := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV s _ le_rfl
  have hftT := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (S.baseChange L f) hV' t _
    le_rfl
  have hNs := BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar S hV s
  have hNt := BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar (S.baseChange L f) hV' t
  have hfLast : LowerDimReductionPullback.baseChangeMapAtLength S L f s t D
      = strictPullbackMapAt s t D t.length le_rfl
        ≫ eqToHom (congrArg s.obj (length_eq_of_strictPullbackBlowupSeq s t D)) :=
    D.lastMap_eq
  have hE : (MaxContactReduction.strictTransformAtLength s H).comap (LowerDimReductionPullback.baseChangeMapAtLength S L f s t D)
      = MaxContactReduction.strictTransformAtLength t
        (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))) :=
    (strictTransformAtLength_comap
      ‹AlgebraicGeometry.Flat (pullback.fst S.structMap (_root_.FunctorialResolution.EmbeddedResolution.specMapOfFieldHom S.base L f))›
      s t D hNs hNt H (LowerDimReductionPullback.baseChangeMapAtLength S L f s t D) hfLast).symm
  have hbcx : LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D [MaxContactReduction.strictTransformAtLength s H]
      = [MaxContactReduction.strictTransformAtLength t
          (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f)))] := by
    show [(MaxContactReduction.strictTransformAtLength s H).comap (LowerDimReductionPullback.baseChangeMapAtLength S L f s t D)] = _
    rw [hE]
  have hsncS : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap)
      ([MaxContactReduction.strictTransformAtLength s H] ++ (s.boundary s.length).drop S.boundary.length) := by
    rw [MaxContactReduction.strictTransformAtLength_eq]
    exact inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar S hV hO H hH s
      (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_iteratedStrictTransform_zero S s H hHsnc) s.length le_rfl
  have hsncT : InStrictNormalCrossingPosition (t.proj t.length ≫ (S.baseChange L f).structMap)
      (LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D [MaxContactReduction.strictTransformAtLength s H] ++
        (t.boundary t.length).drop S.boundary.length) := by
    rw [hbcx, MaxContactReduction.strictTransformAtLength_eq, ← hlen]
    exact inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar (S.baseChange L f) hV' hO'
      (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))) hH' t
      (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_iteratedStrictTransform_zero (S.baseChange L f) t
        (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))) hH'snc) t.length le_rfl
  have hVcS := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV s hftS
    [MaxContactReduction.strictTransformAtLength s H] S.boundary.length hsncS
  have hVcT := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar (S.baseChange L f) hV' t hftT
    (LowerDimReductionPullback.comapBoundaryBaseChange S L f s t D [MaxContactReduction.strictTransformAtLength s H]) S.boundary.length hsncT
  obtain ⟨D2⟩ := nonempty_strictPullbackBlowupSeq_appendLowerDimReduction hderiv hstar hinv P hmono A B hspec T T' hPdimT
    hPdimOther S hV hO hdimS L f hV' hO' hdimS' hbc s t hftS hftT D [MaxContactReduction.strictTransformAtLength s H]
    [MaxContactReduction.strictTransformAtLength t
      (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f)))]
    hbcx.symm S.boundary.length 0 hVcS hVcT (by simp) (by simp [LowerDimReductionPullback.comapBoundaryBaseChange]) hsep hsep'
  exact D2.isStrictPullback

theorem isStrictPullbackBlowupSeq_reduceAlongHypersurface_baseChange
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u}) (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T T' : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (hPdimOther : P T'.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (L : Type u) [Field L] [CharZero L] (f : S.base →+* L)
    [AlgebraicGeometry.Flat (pullback.fst S.structMap (specMapOfFieldHom S.base L f))]
    (hV' : (S.baseChange L f).IsAdmissible)
    (hO' : ∀ x : ↥(S.baseChange L f).scheme,
      orderAt (S.baseChange L f).ideal x ≤ ((S.baseChange L f).mult : ℕ∞))
    (hdim' : (S.baseChange L f).krullDimSucc ≤ T'.krullDimSucc)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    (hH' : ∀ [AlgebraicGeometry.LocallyOfFiniteType (S.baseChange L f).structMap],
      IsMaxContactHypersurface (S.baseChange L f).base (S.baseChange L f).structMap
        (S.baseChange L f).ideal (S.baseChange L f).mult
        (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))))
    (hH'snc : InStrictNormalCrossingPosition (S.baseChange L f).structMap
      [H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))])
    (hbc : IsBaseChangeInherited.{u} P) :
    IsStrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      (MaxContactReduction.reduceAlongHypersurface hinv T' (fun S' _ i => A i S') (S.baseChange L f)
        (H.comap (pullback.fst S.structMap
          (specMapOfFieldHom S.base L f)))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hlen : (S.baseChange L f).boundary.length = S.boundary.length :=
    MarkedIdealWithBoundary.length_boundary_baseChange S L f
  obtain ⟨D⟩ := nonempty_strictPullbackBlowupSeq_separateBoundary hderiv hstar hinv P hmono A B hspec T T'
    hPdimT hPdimOther S hV hO hdimS L f hV' hO' hdim' hbc S.boundary.length le_rfl
  have hSeparated := BoundarySeparationBaseChange.separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T hPdimT
    S hV hO hdimS H hHsnc S.boundary.length le_rfl
  have hSeparatedSeq := BoundarySeparationBaseChange.separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T'
    hPdimOther (S.baseChange L f) hV' hO' hdim'
    (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))) hH'snc
    (S.baseChange L f).boundary.length le_rfl
  rw [hlen] at hSeparatedSeq
  rw [MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction, MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction, hlen]
  exact isStrictPullbackBlowupSeq_appendLowerDimReduction_baseChange hderiv hstar hinv P hmono A B hspec T T' hPdimT hPdimOther S hV
    hO hdimS L f hV' hO' hdim' hbc H hH hHsnc hH' hH'snc
    (MaxContactReduction.separateBoundary hinv T (fun S' _ i => A i S') S S.boundary.length)
    (MaxContactReduction.separateBoundary hinv T' (fun S' _ i => A i S') (S.baseChange L f)
      S.boundary.length)
    D (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated S _ S.boundary.length hSeparated.1)
    (BoundarySeparationBaseChange.orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated (S.baseChange L f) _ S.boundary.length hSeparatedSeq.1)

end BoundaryLoopFieldBaseChange

end FunctorialResolution.EmbeddedResolution

end
