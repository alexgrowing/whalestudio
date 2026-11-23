import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMapSurjective
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusAfterReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.FaithfullyFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SeparateBoundaryFieldBaseChange
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

namespace OrderReductionFieldBaseChange

def dropTrivialBoundaryBaseFieldHom (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : T.base →+* L) :
    (MaxContactReduction.dropTrivialBoundary T).base →+* L := f

def coverBaseFieldHom (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L]
    (f : A.base →+* L) : (MaxContactCoverData.coverTriple A hv).base →+* L := f

theorem coverTriple_structureMorphism_eq (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (MaxContactCoverData.coverTriple T hv).structMap = MaxContactCoverData.coverMap T hv ≫ T.structMap :=
  MaxContactCoverData.coverTriple_structureMorphism T hv

theorem surjective_baseChange_fst (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L]
    (f : T.base →+* L) :
    AlgebraicGeometry.Surjective (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective)
    (CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base L f)).flip
    (FunctorialResolution.EmbeddedResolution.instSurjectiveSpecMapOfFieldHom T.base L f)

theorem orderAtLeastLocus_baseChange_eq_empty (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L]
    (f : T.base →+* L)
    (hord : ∀ y : ↥(T.baseChange L f).scheme,
      orderAt (T.baseChange L f).ideal y
        = orderAt T.ideal ((pullback.fst T.structMap (specMapOfFieldHom T.base L f)) y))
    (hemp : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    orderAtLeastLocus (T.baseChange L f).ideal T.mult = (∅ : Set ↥(T.baseChange L f).scheme) := by
  apply Set.subset_empty_iff.mp
  intro y hy
  have h1 := (mem_orderAtLeastLocus_iff (T.baseChange L f).ideal T.mult y).1 hy
  rw [hord y] at h1
  have h2 : (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) y ∈ orderAtLeastLocus T.ideal T.mult :=
    (mem_orderAtLeastLocus_iff T.ideal T.mult _).2 h1
  rw [hemp] at h2
  simp at h2

def ValidBaseChange : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] [CharZero L] (f : T.base →+* L),
    T.IsAdmissible → (T.baseChange L f).IsAdmissible

def OrderAtBaseChangeEq : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] [CharZero L] (f : T.base →+* L),
    T.IsAdmissible → ∀ y : ↥(T.baseChange L f).scheme,
      orderAt (T.baseChange L f).ideal y
        = orderAt T.ideal ((pullback.fst T.structMap (specMapOfFieldHom T.base L f)) y)

def MaxContactHypersurfaceBaseChange : Prop :=
  ∀ (S : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] [CharZero L] (f : S.base →+* L),
    S.IsAdmissible → (S.baseChange L f).IsAdmissible →
    ∀ H : S.scheme.IdealSheafData,
      (∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
        IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H) →
      InStrictNormalCrossingPosition S.structMap [H] →
      ((∀ [AlgebraicGeometry.LocallyOfFiniteType (S.baseChange L f).structMap],
          IsMaxContactHypersurface (S.baseChange L f).base (S.baseChange L f).structMap
            (S.baseChange L f).ideal (S.baseChange L f).mult
            (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f)))) ∧
        InStrictNormalCrossingPosition (S.baseChange L f).structMap
          [H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))])

private theorem comp_assoc_eq_of_eq_comp {X Y Z W V : Scheme.{u}}
    (p : X ⟶ Y) (q : Y ⟶ W) (b : Y ⟶ Z) (c : Z ⟶ W) (r : X ⟶ V) (s : V ⟶ W)
    (hq : q = b ≫ c) (h : p ≫ q = r ≫ s) :
    (p ≫ b) ≫ c = r ≫ s := by
  rw [Category.assoc, ← hq]
  exact h

theorem coverBaseChangeMap_condition (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L]
    (f : A.base →+* L) :
    (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
        ≫ MaxContactCoverData.coverMap A hv) ≫ A.structMap
      = pullback.snd (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
        ≫ specMapOfFieldHom A.base L f :=
  comp_assoc_eq_of_eq_comp
    (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
    (MaxContactCoverData.coverTriple A hv).structMap
    (MaxContactCoverData.coverMap A hv)
    A.structMap
    (pullback.snd (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
    (specMapOfFieldHom A.base L f)
    (coverTriple_structureMorphism_eq A hv)
    pullback.condition

def coverBaseChangeMap (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L]
    (f : A.base →+* L) :
    ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).scheme ⟶
      (A.baseChange L f).scheme :=
  pullback.lift
    (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
        (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
      ≫ MaxContactCoverData.coverMap A hv)
    (pullback.snd (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
    (coverBaseChangeMap_condition A hv L f)

abbrev coverBaseChangeFiber (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L]
    (f : A.base →+* L) (hv' : (A.baseChange L f).IsAdmissible) : Scheme.{u} :=
  pullback (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)

private theorem decide_eq_true_iff_self (p : Prop) (i : Decidable p) :
    (@decide p i = true) ↔ p := by
  cases i with
  | isTrue h => exact ⟨fun _ => h, fun _ => rfl⟩
  | isFalse h => exact ⟨fun hb => Bool.noConfusion hb, fun hp => absurd hp h⟩

private theorem not_decide_eq_true_iff_not (p : Prop) (i : Decidable p) :
    ((!(@decide p i)) = true) ↔ ¬ p := by
  cases i with
  | isTrue h => exact ⟨fun hb => Bool.noConfusion hb, fun hn => absurd h hn⟩
  | isFalse h => exact ⟨fun _ => h, fun _ => rfl⟩

private theorem nontrivialPart_eq_filter {X : Scheme.{u}}
    {q : X.IdealSheafData → Bool} (hq : ∀ D : X.IdealSheafData, q D = true ↔ D ≠ ⊤)
    (E : List X.IdealSheafData) :
    MarkedIdealWithBoundary.nontrivialPart E = List.filter q E := by
  unfold MarkedIdealWithBoundary.nontrivialPart
  refine congrArg (fun r => List.filter r E) (funext fun D => ?_)
  refine Bool.eq_iff_iff.mpr ?_
  rw [hq D]
  exact not_decide_eq_true_iff_not _ _

private theorem filter_map_comap {X Y : Scheme.{u}} (g : X ⟶ Y)
    (p : Y.IdealSheafData → Bool) (q : X.IdealSheafData → Bool)
    (hpq : ∀ D : Y.IdealSheafData, q (D.comap g) = p D) (E : List Y.IdealSheafData) :
    List.filter q (List.map (fun D => D.comap g) E)
      = List.map (fun D => D.comap g) (List.filter p E) := by
  induction E with
  | nil => simp
  | cons D E ih =>
      cases hD : p D
      · simp [hpq D, hD, ih]
      · simp [hpq D, hD, ih]

private theorem filter_eq_map_filter_of_nontrivialPart_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    [AlgebraicGeometry.Surjective g]
    {p : Y.IdealSheafData → Bool} {q : X.IdealSheafData → Bool}
    {E : List Y.IdealSheafData} {E' : List X.IdealSheafData}
    (hp : ∀ D : Y.IdealSheafData, p D = true ↔ D ≠ ⊤)
    (hq : ∀ D : X.IdealSheafData, q D = true ↔ D ≠ ⊤)
    (hEE : MarkedIdealWithBoundary.nontrivialPart (List.map (fun D => D.comap g) E)
      = MarkedIdealWithBoundary.nontrivialPart E') :
    List.filter q E' = List.map (fun D => D.comap g) (List.filter p E) := by
  have hpq : ∀ D : Y.IdealSheafData, q (D.comap g) = p D := by
    intro D
    refine Bool.eq_iff_iff.mpr ?_
    rw [hq, hp]
    exact comap_ne_top_iff_of_surjective g D
  have h1 : List.filter q (List.map (fun D => D.comap g) E) = List.filter q E' := by
    rw [← nontrivialPart_eq_filter hq (List.map (fun D => D.comap g) E),
      ← nontrivialPart_eq_filter hq E']
    exact hEE
  rw [← h1]
  exact filter_map_comap g p q hpq E

theorem dropTrivialBoundary_withBoundary_baseChange (T : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L]
    (f : T.base →+* L) (E' : List (T.baseChange L f).scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E') :
    MaxContactReduction.dropTrivialBoundary ((T.baseChange L f).withBoundary E')
      = (MaxContactReduction.dropTrivialBoundary T).baseChange L (dropTrivialBoundaryBaseFieldHom T L f) := by
  have hsurj : AlgebraicGeometry.Surjective
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    surjective_baseChange_fst T L f
  have hb : (MaxContactReduction.dropTrivialBoundary ((T.baseChange L f).withBoundary E')).boundary
      = List.map (fun D => D.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
          (MaxContactReduction.dropTrivialBoundary T).boundary := by
    rw [MaxContactReduction.dropTrivialBoundary_boundary, MaxContactReduction.dropTrivialBoundary_boundary,
      MarkedIdealWithBoundary.withBoundary_boundary]
    refine filter_eq_map_filter_of_nontrivialPart_eq
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) ?_ ?_ ?_
    · intro _
      exact decide_eq_true_iff_self _ _
    · intro _
      exact decide_eq_true_iff_self _ _
    · have h := (MarkedIdealWithBoundary.sameNontrivialBoundary_iff ((T.baseChange L f).boundary) E').mp hE
      rw [MarkedIdealWithBoundary.baseChange_boundary] at h
      exact h
  exact congrArg (fun E : List (T.baseChange L f).scheme.IdealSheafData =>
    (T.baseChange L f).withBoundary E) hb

private theorem comap_comap_comap {Q S Y X : Scheme.{u}} (q : Q ⟶ S) (c : S ⟶ Y) (p : Y ⟶ X)
    (I : X.IdealSheafData) : ((I.comap p).comap c).comap q = I.comap (q ≫ c ≫ p) := by
  simp [Scheme.IdealSheafData.comap_comp]

private theorem map_comap_comap_comap {Q S Y X : Scheme.{u}} (q : Q ⟶ S) (c : S ⟶ Y) (p : Y ⟶ X)
    (E : List X.IdealSheafData) :
    List.map (fun D => D.comap q)
        (List.map (fun D => D.comap c) (List.map (fun D => D.comap p) E))
      = List.map (fun D => D.comap (q ≫ c ≫ p)) E := by
  induction E with
  | nil => rfl
  | cons D Es ih => simp only [List.map_cons, comap_comap_comap, ih]

private theorem comap_eq_comap_of_comp_eq {Q S₁ S₂ Y₁ Y₂ X : Scheme.{u}}
    (q₁ : Q ⟶ S₁) (q₂ : Q ⟶ S₂) (c₁ : S₁ ⟶ Y₁) (p₁ : Y₁ ⟶ X) (c₂ : S₂ ⟶ Y₂) (p₂ : Y₂ ⟶ X)
    (I : X.IdealSheafData) (I₁ : S₁.IdealSheafData) (I₂ : S₂.IdealSheafData)
    (h₁ : I₁ = (I.comap p₁).comap c₁) (h₂ : I₂ = (I.comap p₂).comap c₂)
    (hk : q₁ ≫ c₁ ≫ p₁ = q₂ ≫ c₂ ≫ p₂) :
    I₁.comap q₁ = I₂.comap q₂ := by
  subst h₁
  subst h₂
  rw [comap_comap_comap, comap_comap_comap, hk]

private theorem map_comap_eq_map_comap_of_comp_eq {Q S₁ S₂ Y₁ Y₂ X : Scheme.{u}}
    (q₁ : Q ⟶ S₁) (q₂ : Q ⟶ S₂) (c₁ : S₁ ⟶ Y₁) (p₁ : Y₁ ⟶ X) (c₂ : S₂ ⟶ Y₂) (p₂ : Y₂ ⟶ X)
    (E : List X.IdealSheafData) (E₁ : List S₁.IdealSheafData) (E₂ : List S₂.IdealSheafData)
    (h₁ : E₁ = List.map (fun D => D.comap c₁) (List.map (fun D => D.comap p₁) E))
    (h₂ : E₂ = List.map (fun D => D.comap c₂) (List.map (fun D => D.comap p₂) E))
    (hk : q₁ ≫ c₁ ≫ p₁ = q₂ ≫ c₂ ≫ p₂) :
    List.map (fun D => D.comap q₁) E₁ = List.map (fun D => D.comap q₂) E₂ := by
  subst h₁
  subst h₂
  rw [map_comap_comap_comap, map_comap_comap_comap, hk]

private theorem comp_structureMorphism_eq_of_comp_eq {Q S₁ S₂ Y W : Scheme.{u}}
    (q₁ : Q ⟶ S₁) (q₂ : Q ⟶ S₂) (c₁ : S₁ ⟶ Y) (c₂ : S₂ ⟶ Y) (sY : Y ⟶ W)
    (s₁ : S₁ ⟶ W) (s₂ : S₂ ⟶ W)
    (h₁ : s₁ = c₁ ≫ sY) (h₂ : c₂ ≫ sY = s₂) (hpc : q₁ ≫ c₁ = q₂ ≫ c₂) :
    q₁ ≫ s₁ = q₂ ≫ s₂ := by
  subst h₁
  subst h₂
  rw [← Category.assoc, hpc, Category.assoc]

private theorem comp_comp_eq_comp_comp {Q S₁ S₂ Y₁ Y₂ X : Scheme.{u}}
    (q₁ : Q ⟶ S₁) (q₂ : Q ⟶ S₂) (c₁ : S₁ ⟶ Y₁) (p₁ : Y₁ ⟶ X) (cc : S₂ ⟶ Y₁)
    (c₂ : S₂ ⟶ Y₂) (p₂ : Y₂ ⟶ X)
    (hpc : q₁ ≫ c₁ = q₂ ≫ cc) (hcf : cc ≫ p₁ = c₂ ≫ p₂) :
    q₁ ≫ c₁ ≫ p₁ = q₂ ≫ c₂ ≫ p₂ := by
  rw [← Category.assoc, hpc, Category.assoc, hcf]

private theorem markedIdealWithBoundary_mk_congr (k : Type u) [Field k] (Y : Scheme.{u})
    (q q' : Y ⟶ Spec (CommRingCat.of k)) (I I' : Y.IdealSheafData) (m : ℕ)
    (E E' : List Y.IdealSheafData) (hq : q = q') (hI : I = I') (hE : E = E') :
    MarkedIdealWithBoundary.mk k Y q I m E = MarkedIdealWithBoundary.mk k Y q' I' m E' := by
  subst hq
  subst hI
  subst hE
  rfl

theorem pullbackAlong_coverBaseChangeFiber_eq (hderiv : DerivIdealSheafIterateCommBaseChange.{u})
    (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L] [CharZero L]
    (f : A.base →+* L) (hv' : (A.baseChange L f).IsAdmissible) :
    (MaxContactCoverData.coverTriple (A.baseChange L f) hv').pullbackAlong
        (coverBaseChangeFiber A hv L f hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)
          ≫ (MaxContactCoverData.coverTriple (A.baseChange L f) hv').structMap)
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))
      = ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).pullbackAlong
        (coverBaseChangeFiber A hv L f hv')
        (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)
          ≫ ((MaxContactCoverData.coverTriple A hv).baseChange L
              (coverBaseFieldHom A hv L f)).structMap)
        (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f)) := by
  have hcf : coverBaseChangeMap A hv L f ≫ pullback.fst A.structMap (specMapOfFieldHom A.base L f)
      = pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
        ≫ MaxContactCoverData.coverMap A hv := by
    unfold coverBaseChangeMap
    exact pullback.lift_fst _ _ _
  have hcs : coverBaseChangeMap A hv L f ≫ (A.baseChange L f).structMap
      = ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).structMap := by
    simp only [MarkedIdealWithBoundary.baseChange_structureMorphism]
    unfold coverBaseChangeMap
    exact pullback.lift_snd _ _ _
  have hT : MaxContactCoverData.balancedTunedIdeal (A.baseChange L f) hv'
      = (MaxContactCoverData.balancedTunedIdeal A hv).comap
        (pullback.fst A.structMap (specMapOfFieldHom A.base L f)) := by
    have : CharZero A.base := hv.charZero
    have : AlgebraicGeometry.Smooth A.structMap := hv.smooth
    have : AlgebraicGeometry.LocallyOfFiniteType A.structMap := hv.locallyOfFiniteType
    have : AlgebraicGeometry.Smooth (pullback.snd A.structMap (specMapOfFieldHom A.base L f)) :=
      hv'.smooth
    have : AlgebraicGeometry.LocallyOfFiniteType
        (pullback.snd A.structMap (specMapOfFieldHom A.base L f)) := hv'.locallyOfFiniteType
    exact balancedTunedSheaf_comap_of_isPullback hderiv A.base L f A.structMap
      (pullback.snd A.structMap (specMapOfFieldHom A.base L f))
      (pullback.fst A.structMap (specMapOfFieldHom A.base L f))
      (IsPullback.of_hasPullback A.structMap (specMapOfFieldHom A.base L f)) A.ideal A.mult
  have hkey :
      pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)
          ≫ MaxContactCoverData.coverMap (A.baseChange L f) hv'
            ≫ pullback.fst A.structMap (specMapOfFieldHom A.base L f)
        = pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)
          ≫ pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
              (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
            ≫ MaxContactCoverData.coverMap A hv :=
    comp_comp_eq_comp_comp _ _ _ _ (coverBaseChangeMap A hv L f) _ _ pullback.condition hcf
  have hI1 : (MaxContactCoverData.coverTriple (A.baseChange L f) hv').ideal
      = ((MaxContactCoverData.balancedTunedIdeal A hv).comap
          (pullback.fst A.structMap (specMapOfFieldHom A.base L f))).comap
        (MaxContactCoverData.coverMap (A.baseChange L f) hv') := by
    rw [MaxContactCoverData.coverTriple_ideal, hT]
    exact rfl
  have hI2 : ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).ideal
      = ((MaxContactCoverData.balancedTunedIdeal A hv).comap (MaxContactCoverData.coverMap A hv)).comap
        (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))) := by
    rw [MarkedIdealWithBoundary.baseChange_ideal, MaxContactCoverData.coverTriple_ideal]
    exact rfl
  have hE1 : (MaxContactCoverData.coverTriple (A.baseChange L f) hv').boundary
      = List.map (fun D => D.comap (MaxContactCoverData.coverMap (A.baseChange L f) hv'))
        (List.map (fun D => D.comap (pullback.fst A.structMap (specMapOfFieldHom A.base L f)))
          A.boundary) := by
    rw [MaxContactCoverData.coverTriple_boundary, MarkedIdealWithBoundary.baseChange_boundary]
    exact rfl
  have hE2 : ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).boundary
      = List.map (fun D => D.comap
            (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
              (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))))
        (List.map (fun D => D.comap (MaxContactCoverData.coverMap A hv)) A.boundary) := by
    rw [MarkedIdealWithBoundary.baseChange_boundary, MaxContactCoverData.coverTriple_boundary]
    exact rfl
  have hsm :
      pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)
          ≫ (MaxContactCoverData.coverTriple (A.baseChange L f) hv').structMap
        = pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)
          ≫ ((MaxContactCoverData.coverTriple A hv).baseChange L
              (coverBaseFieldHom A hv L f)).structMap :=
    comp_structureMorphism_eq_of_comp_eq _ _ _ _ _ _ _
      (MaxContactCoverData.coverTriple_structureMorphism (A.baseChange L f) hv') hcs pullback.condition
  have hide :
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv').ideal.comap
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f))
        = ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).ideal.comap
          (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)) :=
    comap_eq_comap_of_comp_eq _ _ _ _ _ _ _ _ _ hI1 hI2 hkey
  have hbd :
      List.map
          (fun D => D.comap (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
          (MaxContactCoverData.coverTriple (A.baseChange L f) hv').boundary
        = List.map
          (fun D => D.comap (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
          ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).boundary :=
    map_comap_eq_map_comap_of_comp_eq _ _ _ _ _ _ _ _ _ hE1 hE2 hkey
  exact markedIdealWithBoundary_mk_congr L (coverBaseChangeFiber A hv L f hv') _ _ _ _
    (MaxContactCoverData.coverTriple (A.baseChange L f) hv').mult _ _ hsm hide hbd

private theorem flat_fst_of_isPullback {W X Y Z : Scheme.{u}} {fst : W ⟶ X} {snd : W ⟶ Y}
    {a : X ⟶ Z} {b : Y ⟶ Z} (sq : CategoryTheory.IsPullback fst snd a b)
    (hb : AlgebraicGeometry.Flat b) : AlgebraicGeometry.Flat fst :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Flat) sq.flip hb

private theorem surjective_fst_of_isPullback {W X Y Z : Scheme.{u}} {fst : W ⟶ X} {snd : W ⟶ Y}
    {a : X ⟶ Z} {b : Y ⟶ Z} (sq : CategoryTheory.IsPullback fst snd a b)
    (hb : AlgebraicGeometry.Surjective b) : AlgebraicGeometry.Surjective fst :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) sq.flip hb

private theorem smooth_fst_of_isPullback {W X Y Z : Scheme.{u}} {fst : W ⟶ X} {snd : W ⟶ Y}
    {a : X ⟶ Z} {b : Y ⟶ Z} (sq : CategoryTheory.IsPullback fst snd a b)
    (hb : AlgebraicGeometry.Smooth b) : AlgebraicGeometry.Smooth fst :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Smooth) sq.flip hb

private theorem isPullback_congr_hom {W X Y Z : Scheme.{u}} {fst : W ⟶ X} {snd snd' : W ⟶ Y}
    {a a' : X ⟶ Z} {b : Y ⟶ Z} (h : CategoryTheory.IsPullback fst snd a b)
    (hs : snd' = snd) (ha : a = a') : CategoryTheory.IsPullback fst snd' a' b := by
  subst hs
  subst ha
  exact h

private theorem isPullback_coverBaseChangeMap (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible)
    (L : Type u) [Field L] (f : A.base →+* L) :
    CategoryTheory.IsPullback
      (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
        (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
      (coverBaseChangeMap A hv L f)
      (MaxContactCoverData.coverMap A hv)
      (pullback.fst A.structMap (specMapOfFieldHom A.base L f)) := by
  have hfst : coverBaseChangeMap A hv L f ≫ pullback.fst A.structMap (specMapOfFieldHom A.base L f)
      = pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))
        ≫ MaxContactCoverData.coverMap A hv := pullback.lift_fst _ _ _
  have hsnd : coverBaseChangeMap A hv L f ≫ pullback.snd A.structMap (specMapOfFieldHom A.base L f)
      = pullback.snd (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)) :=
    pullback.lift_snd _ _ _
  refine CategoryTheory.IsPullback.of_bot ?_ hfst.symm
    (CategoryTheory.IsPullback.of_hasPullback A.structMap (specMapOfFieldHom A.base L f))
  exact isPullback_congr_hom
    (CategoryTheory.IsPullback.of_hasPullback (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
    hsnd (coverTriple_structureMorphism_eq A hv)

private theorem isAdmissible_withBoundary_singleton (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (H : S.scheme.IdealSheafData) (hsnc : InStrictNormalCrossingPosition S.structMap [H]) :
    (S.withBoundary [H]).IsAdmissible :=
  ⟨hV.charZero, hV.locallyOfFiniteType, hV.nonzeroOnComponents, hV.one_le_mult,
    hV.quasiCompact, hV.smooth, hsnc⟩

private theorem isStrictPullback_descend_of_flat_surjective_cover
    {XA XB XC XC' XCb XQ : Scheme.{u}}
    (hh : XB ⟶ XA) (g : XC ⟶ XA) (g' : XC' ⟶ XB) (p : XCb ⟶ XB) (pA : XCb ⟶ XC)
    (q₁ : XQ ⟶ XC') (q₂ : XQ ⟶ XCb)
    (hfh : AlgebraicGeometry.Flat hh) (hfq : AlgebraicGeometry.Flat q₁)
    (hfg' : AlgebraicGeometry.Flat g')
    (hsq : AlgebraicGeometry.Surjective q₁) (hsg' : AlgebraicGeometry.Surjective g')
    (hsq1 : q₁ ≫ g' = q₂ ≫ p) (hsq2 : p ≫ hh = pA ≫ g)
    (u : SequenceOfBlowups XQ) (sB : SequenceOfBlowups XC') (sCb : SequenceOfBlowups XCb) (sA : SequenceOfBlowups XC)
    (dA : SequenceOfBlowups XA) (dB : SequenceOfBlowups XB)
    (hX : IsStrictPullbackBlowupSeq q₁ u sB) (hY : IsStrictPullbackBlowupSeq q₂ u sCb)
    (hZ : IsStrictPullbackBlowupSeq pA sCb sA)
    (hdA : IsStrictPullbackBlowupSeq g sA dA) (hdB : IsStrictPullbackBlowupSeq g' sB dB) :
    IsStrictPullbackBlowupSeq hh dB dA := by
  have := hfh
  have := hfq
  have := hfg'
  have := hsq
  have := hsg'
  have hfc : AlgebraicGeometry.Flat (q₁ ≫ g') := inferInstance
  have hsc : AlgebraicGeometry.Surjective (q₁ ≫ g') := inferInstance
  have M1 : IsStrictPullbackBlowupSeq (q₁ ≫ g') u dB := hX.comp hdB
  have M2 : IsStrictPullbackBlowupSeq (q₂ ≫ (pA ≫ g)) u dA := hY.comp (hZ.comp hdA)
  have hcomp : (q₁ ≫ g') ≫ hh = q₂ ≫ (pA ≫ g) := by
    rw [hsq1, Category.assoc, hsq2]
  have M2' : IsStrictPullbackBlowupSeq ((q₁ ≫ g') ≫ hh) u dA := M2.congr_hom hcomp.symm
  have M3 : IsStrictPullbackBlowupSeq (q₁ ≫ g') u (dA.baseChange hh) := M2'.baseChange_of_comp
  have heqv : dB.Isomorphic (dA.baseChange hh) := M1.isomorphic_of_isomorphic M3 (SequenceOfBlowups.isomorphic_refl u)
  exact (isStrictPullbackSequenceOfBlowups_baseChange dA hh).of_isomorphic_pullback heqv.symm

private theorem isStrictPullbackBlowupSeq_coverTriple_baseChange
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u}) (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (Fam : ℕ → PrincipalizationAssignment.{u}) (Bp : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (Fam j) Bp)
    (hinherit : IsBaseChangeInherited.{u} P)
    (hbcV : ValidBaseChange.{u}) (hbcO : OrderAtBaseChangeEq.{u}) (hbcA : MaxContactHypersurfaceBaseChange.{u})
    (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible) (L : Type u) [Field L] [CharZero L] (f : A.base →+* L)
    (hflat : AlgebraicGeometry.Flat (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))))
    (hHyp : MaxContactFunctoriality.OrderReductionHypotheses P A) (hHyp' : MaxContactFunctoriality.OrderReductionHypotheses P (A.baseChange L f))
    (hdimChart : ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).krullDimSucc
      ≤ (A.baseChange L f).krullDimSucc) :
    IsStrictPullbackBlowupSeq
      (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
        (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
      (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
        ((MaxContactCoverData.coverMaxContactIdeal A hv).comap
          (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
            (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L
              (coverBaseFieldHom A hv L f))))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactCoverData.coverMarkedBlowupData A hv hinv (MaxContactFunctoriality.lowerDimensionalFamily Fam A)).toSequenceOfBlowups := by
  have := hflat
  have hVC : (MaxContactCoverData.coverTriple A hv).IsAdmissible :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P A hHyp
  have hVCb : ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).IsAdmissible :=
    hbcV (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVC
  have hadm := hbcA (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVC hVCb
    (MaxContactCoverData.coverMaxContactIdeal A hv)
    (BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P A hHyp)
    (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P A hHyp)
  have hO' : ∀ x : ↥((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).scheme,
      orderAt ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).ideal x
        ≤ ((((MaxContactCoverData.coverTriple A hv).baseChange L
            (coverBaseFieldHom A hv L f)).mult : ℕ) : ℕ∞) := by
    intro x
    rw [hbcO (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVC x]
    exact BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P A hHyp _
  exact BoundaryLoopFieldBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface_baseChange hderiv hstar hinv P hmono Fam Bp hspec
    A (A.baseChange L f) hHyp.dim_prop hHyp'.dim_prop
    (MaxContactCoverData.coverTriple A hv) hVC
    (BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P A hHyp)
    (MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim A hv) L (coverBaseFieldHom A hv L f) hVCb hO' hdimChart
    (MaxContactCoverData.coverMaxContactIdeal A hv)
    (BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P A hHyp)
    (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P A hHyp)
    hadm.1 hadm.2 hinherit

theorem isStrictPullbackBlowupSeq_baseChange_of_cover
    (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u}) (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u})
    (hbcV : ValidBaseChange.{u}) (hbcO : OrderAtBaseChangeEq.{u}) (hbcA : MaxContactHypersurfaceBaseChange.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (Fam : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (Fam j) B)
    (hinherit : IsBaseChangeInherited.{u} P)
    (hcff : MaxContactFunctoriality.CoverFaithfullyFlat.{u} P)
    (A : MarkedIdealWithBoundary.{u}) (hv : A.IsAdmissible)
    (L : Type u) [Field L] [CharZero L] (f : A.base →+* L)
    [AlgebraicGeometry.Flat (pullback.fst A.structMap (specMapOfFieldHom A.base L f))]
    (hv' : (A.baseChange L f).IsAdmissible)
    (hHyp : MaxContactFunctoriality.OrderReductionHypotheses P A)
    (hHyp' : MaxContactFunctoriality.OrderReductionHypotheses P (A.baseChange L f))
    (hdimChart :
      ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).krullDimSucc
        ≤ (A.baseChange L f).krullDimSucc)
    (hqc : AlgebraicGeometry.QuasiCompact
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)
        ≫ ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).structMap))
    (hQdim : krullDimSucc (coverBaseChangeFiber A hv L f hv') ≤ (A.baseChange L f).krullDimSucc)
    (d : BlowupSequenceData A.scheme) (d' : BlowupSequenceData (A.baseChange L f).scheme)
    (hd : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap A hv)
      (MaxContactCoverData.coverMarkedBlowupData A hv hinv (MaxContactFunctoriality.lowerDimensionalFamily Fam A)).toSequenceOfBlowups d.toSequenceOfBlowups)
    (hd' : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap (A.baseChange L f) hv')
      (MaxContactCoverData.coverMarkedBlowupData (A.baseChange L f) hv' hinv
        (MaxContactFunctoriality.lowerDimensionalFamily Fam (A.baseChange L f))).toSequenceOfBlowups d'.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq (pullback.fst A.structMap (specMapOfFieldHom A.base L f)) d'.toSequenceOfBlowups d.toSequenceOfBlowups := by
  have hfA : AlgebraicGeometry.Flat (pullback.fst A.structMap (specMapOfFieldHom A.base L f)) :=
    inferInstance
  have hVCA : (MaxContactCoverData.coverTriple A hv).IsAdmissible :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P A hHyp
  have hVC1 : (MaxContactCoverData.coverTriple (A.baseChange L f) hv').IsAdmissible :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P (A.baseChange L f) hHyp'
  have hVS2 : ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).IsAdmissible :=
    hbcV (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVCA
  have hsqc := isPullback_coverBaseChangeMap A hv L f
  have hfg : AlgebraicGeometry.Flat (MaxContactCoverData.coverMap A hv) :=
    MaxContactCoverData.flat_coverMap_of_isAdmissible A hv
  have hsg : AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap A hv) := (hcff A hHyp).1
  have hsmg : AlgebraicGeometry.Smooth (MaxContactCoverData.coverMap A hv) :=
    MaxContactCoverData.smooth_coverMap_of_isAdmissible A hv
  have hfg' : AlgebraicGeometry.Flat (MaxContactCoverData.coverMap (A.baseChange L f) hv') :=
    MaxContactCoverData.flat_coverMap_of_isAdmissible (A.baseChange L f) hv'
  have hsg' : AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap (A.baseChange L f) hv') :=
    (hcff (A.baseChange L f) hHyp').1
  have hsmg' : AlgebraicGeometry.Smooth (MaxContactCoverData.coverMap (A.baseChange L f) hv') :=
    MaxContactCoverData.smooth_coverMap_of_isAdmissible (A.baseChange L f) hv'
  have hfpA : AlgebraicGeometry.Flat (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))) :=
    flat_fst_of_isPullback hsqc hfA
  have hfp : AlgebraicGeometry.Flat (coverBaseChangeMap A hv L f) :=
    flat_fst_of_isPullback hsqc.flip hfg
  have hsp : AlgebraicGeometry.Surjective (coverBaseChangeMap A hv L f) :=
    surjective_fst_of_isPullback hsqc.flip hsg
  have hsmp : AlgebraicGeometry.Smooth (coverBaseChangeMap A hv L f) :=
    smooth_fst_of_isPullback hsqc.flip hsmg
  have hbig : CategoryTheory.IsPullback
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f) :=
    CategoryTheory.IsPullback.of_hasPullback _ _
  have hfl1 := flat_fst_of_isPullback hbig hfp
  have hsu1 := surjective_fst_of_isPullback hbig hsp
  have hsm1 := smooth_fst_of_isPullback hbig hsmp
  have hfl2 := flat_fst_of_isPullback hbig.flip hfg'
  have hsu2 := surjective_fst_of_isPullback hbig.flip hsg'
  have hsm2 := smooth_fst_of_isPullback hbig.flip hsmg'
  have hT : LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      = LowerDimReductionPullback.pullbackTriple ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
        (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f)) :=
    pullbackAlong_coverBaseChangeFiber_eq hderiv A hv L f hv'
  have hVQ2 : (LowerDimReductionPullback.pullbackTriple
      ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
        (coverBaseChangeMap A hv L f))).IsAdmissible :=
    @OrderReduction.OrderReductionHypotheses.valid_pullbackAlong hin
      ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)) hVS2
      (coverBaseChangeFiber A hv L f hv')
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)
        ≫ ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).structMap)
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      hsm2 hqc rfl
  have hVQ1 : (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
        (coverBaseChangeMap A hv L f))).IsAdmissible := by
    rw [hT]
    exact hVQ2
  have hVb : ((MaxContactCoverData.coverTriple (A.baseChange L f) hv').withBoundary
      [MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv']).IsAdmissible :=
    isAdmissible_withBoundary_singleton (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
      hVC1 (MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv')
      (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P (A.baseChange L f) hHyp')
  have hVQb := @OrderReduction.OrderReductionHypotheses.valid_pullbackAlong hin
    ((MaxContactCoverData.coverTriple (A.baseChange L f) hv').withBoundary
      [MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv']) hVb
    (coverBaseChangeFiber A hv L f hv')
    (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)
      ≫ (MaxContactCoverData.coverTriple (A.baseChange L f) hv').structMap)
    (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
    hsm1 hVQ1.quasiCompact rfl
  have hsncQ1 : InStrictNormalCrossingPosition
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).structMap
      [(MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))] := hVQb.snc
  have hloftQ1 : AlgebraicGeometry.LocallyOfFiniteType
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).structMap := hVQ1.locallyOfFiniteType
  have hadmQ1 : IsMaxContactHypersurface
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).base
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).structMap
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).ideal
      (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))).mult
      ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
          (coverBaseChangeMap A hv L f))) :=
    @hAdm (MaxContactCoverData.coverTriple (A.baseChange L f) hv').base inferInstance hVC1.charZero
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv').scheme
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv').structMap hVC1.smooth
      hVC1.locallyOfFiniteType (coverBaseChangeFiber A hv L f hv')
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      hsm1 hVQ1.locallyOfFiniteType
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv').ideal
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv').mult hVC1.one_le_mult
      (MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv')
      (BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P (A.baseChange L f) hHyp')
  have hadmQ2 := MaxContactFunctoriality.isMaxContactHypersurface_of_triple_eq hT.symm
    hVQ2.locallyOfFiniteType hVQ1.locallyOfFiniteType
    ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
    ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
    HEq.rfl hadmQ1
  have hsncQ2 := MaxContactFunctoriality.inStrictNormalCrossingPosition_of_triple_eq hT.symm
    [(MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))]
    [(MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))]
    HEq.rfl hsncQ1
  have hO2 : ∀ x : ↥((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).scheme,
      orderAt ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)).ideal x
        ≤ ((((MaxContactCoverData.coverTriple A hv).baseChange L
            (coverBaseFieldHom A hv L f)).mult : ℕ) : ℕ∞) := by
    intro x
    rw [hbcO (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVCA x]
    exact BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P A hHyp _
  have hadmS2 := hbcA (MaxContactCoverData.coverTriple A hv) L (coverBaseFieldHom A hv L f) hVCA hVS2
    (MaxContactCoverData.coverMaxContactIdeal A hv)
    (BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P A hHyp)
    (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P A hHyp)
  have hX : IsStrictPullbackBlowupSeq
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
        ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactCoverData.coverMarkedBlowupData (A.baseChange L f) hv' hinv
        (MaxContactFunctoriality.lowerDimensionalFamily Fam (A.baseChange L f))).toSequenceOfBlowups :=
    @BoundarySeparationBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar hin hMC hAdm hinv P hmono Fam B hspec
      (A.baseChange L f) hHyp'.dim_prop
      (MaxContactCoverData.coverTriple (A.baseChange L f) hv') hVC1
      (BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P (A.baseChange L f) hHyp')
      (MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim (A.baseChange L f) hv')
      (MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv')
      (BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P (A.baseChange L f) hHyp')
      (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P (A.baseChange L f) hHyp')
      (coverBaseChangeFiber A hv L f hv')
      (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      hsm1 hfl1 hsu1 hVQ1 hQdim
      ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
      hadmQ1 hsncQ1
  have hY0 : IsStrictPullbackBlowupSeq
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        (LowerDimReductionPullback.pullbackTriple ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
          (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
        ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
        ((MaxContactCoverData.coverMaxContactIdeal A hv).comap
          (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
            (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L
              (coverBaseFieldHom A hv L f))))).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    @BoundarySeparationBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar hin hMC hAdm hinv P hmono Fam B hspec
      (A.baseChange L f) hHyp'.dim_prop
      ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f)) hVS2 hO2 hdimChart
      ((MaxContactCoverData.coverMaxContactIdeal A hv).comap
        (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
          (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f))))
      hadmS2.1 hadmS2.2
      (coverBaseChangeFiber A hv L f hv')
      (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
      hsm2 hfl2 hsu2 hVQ2 hQdim
      ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
      hadmQ2 hsncQ2
  have hEqSeq : (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        (LowerDimReductionPullback.pullbackTriple ((MaxContactCoverData.coverTriple A hv).baseChange L (coverBaseFieldHom A hv L f))
          (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
        ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      = (MaxContactReduction.reduceAlongHypersurface hinv (A.baseChange L f) (fun S' _ i => Fam i S')
        (LowerDimReductionPullback.pullbackTriple (MaxContactCoverData.coverTriple (A.baseChange L f) hv')
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))
        ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
          (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv')
            (coverBaseChangeMap A hv L f)))).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    eq_of_heq (MaxContactFunctoriality.reduceAlongHypersurface_toSequenceOfBlowups_heq hinv (A.baseChange L f)
      (fun S' _ i => Fam i S') hT.symm
      ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
      ((MaxContactCoverData.coverMaxContactIdeal (A.baseChange L f) hv').comap
        (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f)))
      HEq.rfl)
  have hY := hY0.congr_sourceSeq hEqSeq
  have hZ := isStrictPullbackBlowupSeq_coverTriple_baseChange hderiv hstar hinv P hmono Fam B hspec hinherit
    hbcV hbcO hbcA A hv L f hfpA hHyp hHyp' hdimChart
  exact isStrictPullback_descend_of_flat_surjective_cover (pullback.fst A.structMap (specMapOfFieldHom A.base L f))
    (MaxContactCoverData.coverMap A hv) (MaxContactCoverData.coverMap (A.baseChange L f) hv')
    (coverBaseChangeMap A hv L f)
    (pullback.fst (MaxContactCoverData.coverTriple A hv).structMap
      (specMapOfFieldHom (MaxContactCoverData.coverTriple A hv).base L (coverBaseFieldHom A hv L f)))
    (pullback.fst (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
    (pullback.snd (MaxContactCoverData.coverMap (A.baseChange L f) hv') (coverBaseChangeMap A hv L f))
    hfA hfl1 hfg' hsu1 hsg' pullback.condition hsqc.w.symm
    _ _ _ _ _ _ hX hY hZ hd hd'

private theorem isStrictPullback_of_eq_of_heq
    (hinv : ComapIsoInvariance.{u}) (Fam : ℕ → PrincipalizationAssignment.{u})
    {T₁ T₂ : MarkedIdealWithBoundary.{u}} (hT : T₁ = T₂)
    (hv₁ : T₁.IsAdmissible) (hv₂ : T₂.IsAdmissible) (d : BlowupSequenceData T₁.scheme)
    {Z : Scheme.{u}} (ψ : T₁.scheme ⟶ Z) (ψ' : T₂.scheme ⟶ Z) (hψ : HEq ψ ψ')
    (w : SequenceOfBlowups Z)
    (hcrit : ∀ e : BlowupSequenceData T₂.scheme,
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T₂ hv₂)
          (MaxContactCoverData.coverMarkedBlowupData T₂ hv₂ hinv
            (MaxContactFunctoriality.lowerDimensionalFamily Fam T₂)).toSequenceOfBlowups e.toSequenceOfBlowups →
        IsStrictPullbackBlowupSeq ψ' e.toSequenceOfBlowups w)
    (hd : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T₁ hv₁)
      (MaxContactCoverData.coverMarkedBlowupData T₁ hv₁ hinv
        (MaxContactFunctoriality.lowerDimensionalFamily Fam T₁)).toSequenceOfBlowups d.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq ψ d.toSequenceOfBlowups w := by
  subst hT
  have hψ2 : ψ = ψ' := eq_of_heq hψ
  subst hψ2
  exact hcrit d hd

theorem isStrictPullbackBlowupSeq_baseChange_withBoundary
    (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u}) (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u})
    (hbcV : ValidBaseChange.{u}) (hbcO : OrderAtBaseChangeEq.{u}) (hbcA : MaxContactHypersurfaceBaseChange.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (Fam : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (Fam j) B)
    (hinherit : IsBaseChangeInherited.{u} P)
    (hsf : MaxContactFunctoriality.CoverSequenceProperties hinv P Fam)
    (hmd : MaxContactFunctoriality.MarkingDescends hinv P Fam)
    (hcff : MaxContactFunctoriality.CoverFaithfullyFlat.{u} P)
    (htv : MaxContactFunctoriality.DropTrivialBoundaryAdmissible.{u})
    (htm : MaxContactFunctoriality.MarkedOfMarkedDropTrivialBoundary.{u})
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
    [AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f))]
    (E' : List (T.baseChange L f).scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange L f).boundary E')
    (hV' : ((T.baseChange L f).withBoundary E').IsAdmissible)
    (hP' : P ((T.baseChange L f).withBoundary E').krullDimSucc)
    (hdimChart :
      ((MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) (htv T hV)).baseChange L
          (coverBaseFieldHom (MaxContactReduction.dropTrivialBoundary T) (htv T hV) L (dropTrivialBoundaryBaseFieldHom T L f))).krullDimSucc
        ≤ (T.baseChange L f).krullDimSucc)
    (hqc : AlgebraicGeometry.QuasiCompact
      (pullback.snd
          (MaxContactCoverData.coverMap ((MaxContactReduction.dropTrivialBoundary T).baseChange L (dropTrivialBoundaryBaseFieldHom T L f))
            (hbcV (MaxContactReduction.dropTrivialBoundary T) L (dropTrivialBoundaryBaseFieldHom T L f) (htv T hV)))
          (coverBaseChangeMap (MaxContactReduction.dropTrivialBoundary T) (htv T hV) L (dropTrivialBoundaryBaseFieldHom T L f))
        ≫ ((MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) (htv T hV)).baseChange L
            (coverBaseFieldHom (MaxContactReduction.dropTrivialBoundary T) (htv T hV) L (dropTrivialBoundaryBaseFieldHom T L f))).structMap))
    (hQdim : krullDimSucc
        (coverBaseChangeFiber (MaxContactReduction.dropTrivialBoundary T) (htv T hV) L (dropTrivialBoundaryBaseFieldHom T L f)
          (hbcV (MaxContactReduction.dropTrivialBoundary T) L (dropTrivialBoundaryBaseFieldHom T L f) (htv T hV)))
      ≤ (T.baseChange L f).krullDimSucc) :
    IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (MaxContactFunctoriality.maxContactPrincipalization hinv Fam ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups
      (MaxContactFunctoriality.maxContactPrincipalization hinv Fam T).toSequenceOfBlowups := by
  have hord : ∀ y : ↥(T.baseChange L f).scheme,
      orderAt (T.baseChange L f).ideal y
        = orderAt T.ideal ((pullback.fst T.structMap (specMapOfFieldHom T.base L f)) y) :=
    hbcO T L f hV
  have hord' : ∀ x : ↥((T.baseChange L f).withBoundary E').scheme,
      orderAt ((T.baseChange L f).withBoundary E').ideal x
        ≤ ((((T.baseChange L f).withBoundary E').mult : ℕ) : ℕ∞) := by
    intro x
    exact (hord x).le.trans (hO _)
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · have h1 : (MaxContactFunctoriality.maxContactPrincipalization hinv Fam T).length = 0 :=
      MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P Fam T hV hP hO hemp
    have hemp' : orderAtLeastLocus ((T.baseChange L f).withBoundary E').ideal
        ((T.baseChange L f).withBoundary E').mult = ∅ :=
      orderAtLeastLocus_baseChange_eq_empty T L f hord hemp
    have h2 : (MaxContactFunctoriality.maxContactPrincipalization hinv Fam
        ((T.baseChange L f).withBoundary E')).length = 0 :=
      MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P Fam
        ((T.baseChange L f).withBoundary E') hV' hP' hord' hemp'
    exact IsStrictPullbackBlowupSeq.of_length_zero
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (MaxContactFunctoriality.maxContactPrincipalization hinv Fam ((T.baseChange L f).withBoundary E')).toSequenceOfBlowups
      (MaxContactFunctoriality.maxContactPrincipalization hinv Fam T).toSequenceOfBlowups h2 h1
  · have hHypT : MaxContactFunctoriality.OrderReductionHypotheses P T :=
      ⟨hP, hO, Set.nonempty_iff_ne_empty.mpr hemp, hV⟩
    have hHypT' : MaxContactFunctoriality.OrderReductionHypotheses P ((T.baseChange L f).withBoundary E') := by
      have hsurjfst := surjective_baseChange_fst T L f
      refine ⟨hP', hord', ?_, hV'⟩
      by_contra hcon
      exact hemp (orderAtLeastLocus_eq_empty_of_comap_eq_empty
        (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) T.ideal T.mult
        (Set.not_nonempty_iff_eq_empty.mp hcon))
    obtain ⟨d, hd, hmain⟩ :=
      MaxContactFunctoriality.exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm T hHypT
    obtain ⟨d', hd', hmain'⟩ :=
      MaxContactFunctoriality.exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm
        ((T.baseChange L f).withBoundary E') hHypT'
    rw [hmain, hmain']
    have hT : MaxContactReduction.dropTrivialBoundary ((T.baseChange L f).withBoundary E')
        = (MaxContactReduction.dropTrivialBoundary T).baseChange L (dropTrivialBoundaryBaseFieldHom T L f) :=
      dropTrivialBoundary_withBoundary_baseChange T L f E' hE
    have hflat : AlgebraicGeometry.Flat
        (pullback.fst (MaxContactReduction.dropTrivialBoundary T).structMap
          (specMapOfFieldHom (MaxContactReduction.dropTrivialBoundary T).base L (dropTrivialBoundaryBaseFieldHom T L f))) :=
      inferInstanceAs
        (AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
    have hHypBC : MaxContactFunctoriality.OrderReductionHypotheses P
        ((MaxContactReduction.dropTrivialBoundary T).baseChange L (dropTrivialBoundaryBaseFieldHom T L f)) := by
      rw [← hT]
      exact hHypT'.of_dropTrivialBoundaryAdmissible htv
    refine isStrictPullback_of_eq_of_heq hinv Fam hT ((hHypT'.of_dropTrivialBoundaryAdmissible htv).valid)
      (hbcV (MaxContactReduction.dropTrivialBoundary T) L (dropTrivialBoundaryBaseFieldHom T L f) (htv T hV)) d'
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) HEq.rfl d.toSequenceOfBlowups ?_ hd'
    intro e he
    exact isStrictPullbackBlowupSeq_baseChange_of_cover hstar hin hMC hAdm hderiv hbcV hbcO hbcA hinv P
      hmono Fam B hspec hinherit hcff (MaxContactReduction.dropTrivialBoundary T) (htv T hV) L (dropTrivialBoundaryBaseFieldHom T L f)
      (hbcV (MaxContactReduction.dropTrivialBoundary T) L (dropTrivialBoundaryBaseFieldHom T L f) (htv T hV))
      (hHypT.of_dropTrivialBoundaryAdmissible htv) hHypBC hdimChart hqc hQdim d e hd he

end OrderReductionFieldBaseChange

end FunctorialResolution.EmbeddedResolution

end
