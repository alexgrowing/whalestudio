import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace StrictPullbackBlowupSeq

theorem smooth_map {X' X : Scheme.{u}} {g : X' ⟶ X} [AlgebraicGeometry.Smooth g]
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (D : StrictPullbackBlowupSeq g t s)
    (i : ℕ) (hi : i ≤ t.length) : AlgebraicGeometry.Smooth (D.comp i hi) := by
  have hsq : IsPullback (D.comp i hi) (t.projectionToBase i) (s.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero
      D.pullback i hi
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) := inferInstance
  exact hbc.of_isPullback hsq.flip ‹AlgebraicGeometry.Smooth g›

end StrictPullbackBlowupSeq

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem ideal_congr_index (u : MarkedBlowupSequenceData p I m E) {i j : ℕ} (h : i = j) :
    u.ideal i = (u.ideal j).comap (eqToHom (congrArg (fun n => u.obj n) h)) := by
  subst h
  simp

theorem boundary_congr_index (u : MarkedBlowupSequenceData p I m E) {i j : ℕ} (h : i = j) :
    u.boundary i =
      (u.boundary j).map (fun A => A.comap (eqToHom (congrArg (fun n => u.obj n) h))) := by
  subst h
  simp

end MarkedBlowupSequenceData

theorem IsStrictPullbackBlowupSeq.of_eq {X' X : Scheme.{u}} {φ : X' ⟶ X} {B₁ B₂ : SequenceOfBlowups X'}
    {C₁ C₂ : SequenceOfBlowups X} (h₁ : B₁ = B₂) (h₂ : C₁ = C₂)
    (hh : IsStrictPullbackBlowupSeq φ B₁ C₁) : IsStrictPullbackBlowupSeq φ B₂ C₂ := by
  subst h₁
  subst h₂
  exact hh

namespace LowerDimReductionPullback

@[reducible] noncomputable def pullbackTriple (S : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (g : Y ⟶ S.scheme) : MarkedIdealWithBoundary.{u} :=
  S.pullbackAlong Y (g ≫ S.structMap) g

variable (S : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ S.scheme)
  (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  (t : MarkedBlowupSequenceData (pullbackTriple S g).structMap (pullbackTriple S g).ideal (pullbackTriple S g).mult
      (pullbackTriple S g).boundary)
  (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)

noncomputable def pullbackMapAtLength : t.obj t.length ⟶ s.obj s.length :=
  D.lastMap

theorem pullbackMapAtLength_eq_lastMap : pullbackMapAtLength S g s t D = D.lastMap := rfl

@[reducible] noncomputable def comapBoundaryPullback (L : List (s.obj s.length).IdealSheafData) :
    List (t.obj t.length).IdealSheafData :=
  L.map (fun A => A.comap (pullbackMapAtLength S g s t D))

private theorem eqToHom_comp_projectionToBase {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ}
    (h : a = b) :
    eqToHom (congrArg (fun n => s.schemeAt n) h) ≫ s.projectionToBase b = s.projectionToBase a := by
  subst h
  simp

private theorem lastMap_comp_projectionToBase {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (D : StrictPullbackBlowupSeq g t s) :
    D.lastMap ≫ s.projectionToBase s.length = t.projectionToBase t.length ≫ g := by
  have key := isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero
    D.pullback t.length le_rfl
  rw [StrictPullbackBlowupSeq.lastMap_eq, Category.assoc, eqToHom_comp_projectionToBase s D.length_eq]
  exact key.w

theorem pullbackMapAtLength_comp_eq_comp_structureMorphism :
    pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap) =
      t.proj t.length ≫ (g ≫ S.structMap) := by
  have h2 : pullbackMapAtLength S g s t D ≫ s.proj s.length = t.proj t.length ≫ g := by
    rw [MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups s s.length,
      MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups t t.length]
    exact lastMap_comp_projectionToBase D
  have h3 : (pullbackMapAtLength S g s t D ≫ s.proj s.length) ≫ S.structMap
      = (t.proj t.length ≫ g) ≫ S.structMap :=
    congrArg (fun φ : t.obj t.length ⟶ S.scheme => φ ≫ S.structMap) h2
  exact (Category.assoc _ _ _).symm.trans (h3.trans (Category.assoc _ _ _))

theorem pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism :
    pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap) =
      t.proj t.length ≫ (pullbackTriple S g).structMap := by
  have h : g ≫ S.structMap = (pullbackTriple S g).structMap :=
    (MarkedIdealWithBoundary.pullbackAlong_structureMorphism S Y (g ≫ S.structMap) g).symm
  refine (pullbackMapAtLength_comp_eq_comp_structureMorphism S g s t D).trans ?_
  exact congrArg (fun f => t.proj t.length ≫ f) h

private theorem comap_eq_comap_comp_eqToHom
    (F : ℕ → Scheme.{u}) (J : ∀ n : ℕ, (F n).IdealSheafData) {a b : ℕ} (hab : a = b)
    {Z : Scheme.{u}} (f : Z ⟶ F a) :
    (J a).comap f = (J b).comap (f ≫ eqToHom (congrArg F hab)) := by
  subst hab
  simp

theorem ideal_eq_comap_pullbackMapAtLength :
    t.ideal t.length = (s.ideal s.length).comap (pullbackMapAtLength S g s t D) := by
  have hL : t.length = s.length := D.length_eq
  have key := MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform (I := S.ideal) (m := S.mult) (E := S.boundary)
    (d := s.toBlowupSequenceData) t D s.isMarked.divisible t.length le_rfl
  refine key.trans ?_
  rw [s.controlledTransform_eq_ideal t.length hL.le]
  exact comap_eq_comap_comp_eqToHom s.obj s.ideal hL _

private theorem boundary_eq_map_comap_strictPullbackComparisonMap {K : Type u} [Field K] {XX' XX : Scheme.{u}}
    {qq : XX' ⟶ Spec (CommRingCat.of K)} {gg : XX' ⟶ XX} [AlgebraicGeometry.Flat gg]
    {II : XX.IdealSheafData} {mm : ℕ} {EE : List XX.IdealSheafData} {dd : BlowupSequenceData XX}
    (tt : MarkedBlowupSequenceData qq (II.comap gg) mm (EE.map fun A => A.comap gg))
    (DD : StrictPullbackBlowupSeq gg tt.toMarkedSequenceOfBlowups.toSequenceOfBlowups dd.toSequenceOfBlowups)
    (hNd : ∀ i ≤ dd.length, AlgebraicGeometry.IsLocallyNoetherian (dd.obj i))
    (hNt : ∀ i ≤ tt.length, AlgebraicGeometry.IsLocallyNoetherian (tt.obj i))
    (i j : ℕ) (hi : i ≤ tt.length) (hij : i = j) :
    tt.boundary i =
      (dd.boundaryFrom EE j).map
        (fun A => A.comap (tt.strictPullbackComparisonMap DD i hi ≫ eqToHom (congrArg (fun n => dd.obj n) hij))) := by
  subst hij
  simp only [eqToHom_refl, Category.comp_id]
  exact tt.boundary_eq_comap_strictPullbackComparisonMap DD hNd hNt i hi

theorem boundary_eq_map_comap_pullbackMapAtLength [AlgebraicGeometry.Flat g]
    (hNs : ∀ i ≤ s.length, AlgebraicGeometry.IsLocallyNoetherian (s.obj i))
    (hNt : ∀ i ≤ t.length, AlgebraicGeometry.IsLocallyNoetherian (t.obj i)) :
    t.boundary t.length =
      (s.boundary s.length).map (fun A => A.comap (pullbackMapAtLength S g s t D)) := by
  have hlen : t.length = s.length := D.length_eq
  have key := boundary_eq_map_comap_strictPullbackComparisonMap (dd := s.toBlowupSequenceData) (II := S.ideal) (mm := S.mult)
    (EE := S.boundary) (gg := g) t D hNs hNt t.length s.length le_rfl hlen
  rw [MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq s s.length le_rfl] at key
  exact key

private theorem smooth_comp_eqToHom {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (h : Y = Y')
    (hf : AlgebraicGeometry.Smooth f) : AlgebraicGeometry.Smooth (f ≫ eqToHom h) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  exact hf

private theorem smooth_lastMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    [AlgebraicGeometry.Smooth g] {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) : AlgebraicGeometry.Smooth D.lastMap := by
  rw [StrictPullbackBlowupSeq.lastMap_eq]
  exact smooth_comp_eqToHom _ _ (StrictPullbackBlowupSeq.smooth_map D t.length le_rfl)

theorem smooth_pullbackMapAtLength [AlgebraicGeometry.Smooth g] :
    AlgebraicGeometry.Smooth (pullbackMapAtLength S g s t D) := by
  rw [pullbackMapAtLength_eq_lastMap]
  exact smooth_lastMap D

private theorem surjective_comp_eqToHom {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (hf : AlgebraicGeometry.Surjective f) (h : Y = Z) :
    AlgebraicGeometry.Surjective (f ≫ eqToHom h) := by
  subst h
  rw [eqToHom_refl, Category.comp_id]
  exact hf

private theorem surjective_lastMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    [AlgebraicGeometry.Surjective g] {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) : AlgebraicGeometry.Surjective D.lastMap := by
  rw [StrictPullbackBlowupSeq.lastMap_eq]
  exact surjective_comp_eqToHom _
    (surjective_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero D.pullback
      t.length le_rfl) _

theorem surjective_pullbackMapAtLength [AlgebraicGeometry.Surjective g] :
    AlgebraicGeometry.Surjective (pullbackMapAtLength S g s t D) := by
  rw [pullbackMapAtLength_eq_lastMap]
  exact surjective_lastMap D

private theorem balancedTunedSheaf_congr (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} {p q : X ⟶ Spec (CommRingCat.of k)} (hpq : p = q)
    (hp : AlgebraicGeometry.LocallyOfFiniteType p)
    (hq : AlgebraicGeometry.LocallyOfFiniteType q)
    {I J : X.IdealSheafData} (hIJ : I = J) {m n : ℕ} (hmn : m = n) :
    @balancedTunedSheaf k _ _ X p hp I m = @balancedTunedSheaf k _ _ X q hq J n := by
  subst hpq
  subst hIJ
  subst hmn
  rfl

theorem tunedIdealAtLength_comap_pullbackMapAtLength [AlgebraicGeometry.Smooth g]
    (hftS : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : AlgebraicGeometry.LocallyOfFiniteType (t.proj t.length ≫ (pullbackTriple S g).structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsAdmissible) :
    (tunedIdealAtLength S s hftS).comap (pullbackMapAtLength S g s t D) = tunedIdealAtLength (pullbackTriple S g) t hftT := by
  have hmor : pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap)
      = t.proj t.length ≫ (pullbackTriple S g).structMap := pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D
  have hid : t.ideal t.length = (s.ideal s.length).comap (pullbackMapAtLength S g s t D) :=
    ideal_eq_comap_pullbackMapAtLength S g s t D
  have hsm : AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap) := by
    have h0 := hVc.smooth
    rwa [structureMorphism_derivedTriple S s hftS extra keep] at h0
  have := hftS
  have := hftT
  have := smooth_pullbackMapAtLength S g s t D
  have : AlgebraicGeometry.LocallyOfFiniteType
      (pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap)) := by
    rw [hmor]
    exact hftT
  rw [tunedIdealAtLength_eq_balancedTunedSheaf, tunedIdealAtLength_eq_balancedTunedSheaf,
    ← balancedTunedSheaf_comap S.base (s.proj s.length ≫ S.structMap) (pullbackMapAtLength S g s t D)
      (s.ideal s.length) S.mult]
  exact balancedTunedSheaf_congr S.base hmor _ _ hid.symm
    (MarkedIdealWithBoundary.pullbackAlong_mult S Y (g ≫ S.structMap) g).symm

theorem pullbackAlong_derivedTriple_eq [AlgebraicGeometry.Smooth g]
    (hftS : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : AlgebraicGeometry.LocallyOfFiniteType (t.proj t.length ≫ (pullbackTriple S g).structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsAdmissible) :
    ((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (t.obj t.length)
          (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
          (pullbackMapAtLength S g s t D)).withBoundary
        (@List.append (t.obj t.length).IdealSheafData (comapBoundaryPullback S g s t D extra)
          ((t.boundary t.length).drop keep)) =
      MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT (comapBoundaryPullback S g s t D extra) keep := by
  have hstruct : pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ S.structMap)
      = t.proj t.length ≫ (pullbackTriple S g).structMap := pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D
  have hideal : (tunedIdealAtLength S s hftS).comap (pullbackMapAtLength S g s t D) = tunedIdealAtLength (pullbackTriple S g) t hftT :=
    tunedIdealAtLength_comap_pullbackMapAtLength S g s t D hftS hftT extra keep hVc
  simp only [MaxContactCoverData.derivedTriple, MarkedIdealWithBoundary.pullbackAlong, MarkedIdealWithBoundary.withBoundary]
  congr 1

private theorem map_comap_append_drop {X₁ X₂ : Scheme.{u}} (f : X₁ ⟶ X₂)
    (E Bd : List X₂.IdealSheafData) (Bd' : List X₁.IdealSheafData) (n : ℕ)
    (h : Bd' = Bd.map (fun A' => A'.comap f)) :
    List.map (fun Dv : X₂.IdealSheafData => Dv.comap f) (E ++ Bd.drop n)
      = List.map (fun Dv : X₂.IdealSheafData => Dv.comap f) E ++ Bd'.drop n := by
  subst h
  rw [List.map_append, List.map_drop]

private theorem isStrictPullbackBlowupSeq_of_isBoundaryDivisorReduction {P : ℕ → Prop} {jj : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsBoundaryDivisorReduction P jj A B) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc)
    (hO : T.IsOrderBoundedByMult)
    (hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap) (hD : T.IsBalanced hft)
    (hjb : jj < T.boundary.length)
    (Yv : Scheme.{u}) (q : Yv ⟶ Spec (CommRingCat.of T.base)) (h : Yv ⟶ T.scheme)
    (hsm : AlgebraicGeometry.Smooth h) (hsu : AlgebraicGeometry.Surjective h)
    (hq : h ≫ T.structMap = q) (E' : List Yv.IdealSheafData)
    (hbe : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Yv q h).boundary E')
    (htake : List.take (jj + 1) E' = List.take (jj + 1) (T.pullbackAlong Yv q h).boundary)
    (hV2 : ((T.pullbackAlong Yv q h).withBoundary E').IsAdmissible)
    (hP2 : P ((T.pullbackAlong Yv q h).withBoundary E').krullDimSucc)
    (hO2 : ((T.pullbackAlong Yv q h).withBoundary E').IsOrderBoundedByMult)
    (hft2 : AlgebraicGeometry.LocallyOfFiniteType
      ((T.pullbackAlong Yv q h).withBoundary E').structMap)
    (hD2 : ((T.pullbackAlong Yv q h).withBoundary E').IsBalanced hft2)
    (hjb2 : jj < ((T.pullbackAlong Yv q h).withBoundary E').boundary.length) :
    IsStrictPullbackBlowupSeq h (A ((T.pullbackAlong Yv q h).withBoundary E')).toSequenceOfBlowups
      (A T).toSequenceOfBlowups := by
  have := hsm
  have := hsu
  exact hspec.smooth_pullback_strict T hV hP hO hD hjb Yv q h hq E' hbe htake hV2 hP2 hO2 hD2 hjb2

theorem nonempty_strictPullback_appendLowerDimReduction [AlgebraicGeometry.Smooth g] [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Surjective g]
    (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u}) (j : ℕ)
    (hspec : IsBoundaryDivisorReduction P j (A j) B)
    (rc : (S' : MarkedIdealWithBoundary.{u}) → S'.krullDimSucc ≤ T.krullDimSucc → ℕ → S'.SequenceOfBlowups)
    (hrc : ∀ (S' : MarkedIdealWithBoundary.{u}) (h : S'.krullDimSucc ≤ T.krullDimSucc) (i : ℕ), rc S' h i = A i S')
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hftS : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : AlgebraicGeometry.LocallyOfFiniteType (t.proj t.length ≫ (pullbackTriple S g).structMap))
    (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hNs : ∀ i ≤ s.length, AlgebraicGeometry.IsLocallyNoetherian (s.obj i))
    (hV' : (pullbackTriple S g).IsAdmissible)
    (hO' : ∀ x : ↥(pullbackTriple S g).scheme,
      orderAt (pullbackTriple S g).ideal x ≤ (((pullbackTriple S g).mult : ℕ) : ℕ∞))
    (hNt : ∀ i ≤ t.length, AlgebraicGeometry.IsLocallyNoetherian (t.obj i))
    (hdim : (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc ≤ T.krullDimSucc)
    (hP : P (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsAdmissible)
    (hj : j < (extra ++ (s.boundary s.length).drop keep).length)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take keep,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : Set ↥(s.obj s.length)) = ∅)
    (hdim' : (MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep).krullDimSucc ≤ T.krullDimSucc)
    (hP' : P (MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep).krullDimSucc)
    (hVc' : (MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep).IsAdmissible)
    (hj' : j < (@List.append (t.obj t.length).IdealSheafData
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap)
      ((t.boundary t.length).drop keep)).length)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take keep,
      orderAtLeastLocus (t.ideal t.length) (pullbackTriple S g).mult ∩
        (Dv.support : Set ↥(t.obj t.length)) = ∅) :
    Nonempty (StrictPullbackBlowupSeq g
      (MaxContactReduction.appendLowerDimReduction hinv T rc (pullbackTriple S g) t
        (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap)
        keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T rc S s extra keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  have hsm : AlgebraicGeometry.Smooth (pullbackMapAtLength S g s t D) := smooth_pullbackMapAtLength S g s t D
  have hsu : AlgebraicGeometry.Surjective (pullbackMapAtLength S g s t D) := surjective_pullbackMapAtLength S g s t D
  have hmult : (pullbackTriple S g).mult = S.mult :=
    MarkedIdealWithBoundary.pullbackAlong_mult S Y (g ≫ S.structMap) g
  have hm' : 1 ≤ (pullbackTriple S g).mult := le_of_le_of_eq hm hmult.symm
  have hb1 : (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary
      = extra ++ (s.boundary s.length).drop keep := rfl
  have hbd : ((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (t.obj t.length)
        (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
        (pullbackMapAtLength S g s t D)).boundary
      = comapBoundaryPullback S g s t D extra ++ (t.boundary t.length).drop keep := by
    refine (MarkedIdealWithBoundary.pullbackAlong_boundary (MaxContactCoverData.derivedTriple S s hftS extra keep)
        (t.obj t.length)
        (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
        (pullbackMapAtLength S g s t D)).trans ?_
    exact map_comap_append_drop (pullbackMapAtLength S g s t D) extra (s.boundary s.length)
      (t.boundary t.length) keep (boundary_eq_map_comap_pullbackMapAtLength S g s t D hNs hNt)
  have hbe : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (t.obj t.length)
        (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
        (pullbackMapAtLength S g s t D)).boundary
      (comapBoundaryPullback S g s t D extra ++ (t.boundary t.length).drop keep) := by
    have hrefl : ∀ L L' : List (t.obj t.length).IdealSheafData,
        L = L' → MarkedIdealWithBoundary.SameNontrivialBoundary L L' := by
      rintro L L' rfl
      exact MarkedIdealWithBoundary.SameNontrivialBoundary.refl L
    exact hrefl _ _ hbd
  have htake : List.take (j + 1) (comapBoundaryPullback S g s t D extra ++ (t.boundary t.length).drop keep)
      = List.take (j + 1)
          (((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (t.obj t.length)
            (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
            (pullbackMapAtLength S g s t D)).boundary) :=
    congrArg (fun l => List.take (j + 1) l) hbd.symm
  have hkey : ((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (t.obj t.length)
        (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
        (pullbackMapAtLength S g s t D)).withBoundary
        (comapBoundaryPullback S g s t D extra ++ (t.boundary t.length).drop keep)
      = MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
          (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep :=
    pullbackAlong_derivedTriple_eq S g s t D hftS hftT extra keep hVc
  have hO1 : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsOrderBoundedByMult :=
    isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  have hD1 := isBalanced_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  have hjb1 : j < (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary.length := by
    rw [hb1]
    exact hj
  have hO2' := isOrderBoundedByMult_derivedTriple hstar (pullbackTriple S g) hV' hm' hO' t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep hVc'
  have hD2' := isBalanced_derivedTriple hstar (pullbackTriple S g) hV' hm' hO' t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep hVc'
  have hfacts : ∀ T' : MarkedIdealWithBoundary.{u},
      T' = MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
        (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep →
      T'.IsAdmissible ∧ P T'.krullDimSucc ∧ T'.IsOrderBoundedByMult ∧ j < T'.boundary.length ∧
        ∀ hft : AlgebraicGeometry.LocallyOfFiniteType T'.structMap, T'.IsBalanced hft := by
    rintro T' rfl
    exact ⟨hVc', hP', hO2', hj', fun _ => hD2'⟩
  obtain ⟨hV2, hP2, hO2, hjb2, hD2⟩ := hfacts _ hkey
  have h0 := isStrictPullbackBlowupSeq_of_isBoundaryDivisorReduction hspec (MaxContactCoverData.derivedTriple S s hftS extra keep)
      hVc hP hO1 _ hD1 hjb1 (t.obj t.length)
      (pullbackMapAtLength S g s t D ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
      (pullbackMapAtLength S g s t D) hsm hsu rfl
      (comapBoundaryPullback S g s t D extra ++ (t.boundary t.length).drop keep) hbe htake
      hV2 hP2 hO2 hV2.locallyOfFiniteType (hD2 hV2.locallyOfFiniteType) hjb2
  have hspb : IsStrictPullbackBlowupSeq (pullbackMapAtLength S g s t D)
      (A j (MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
        (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep)).toSequenceOfBlowups
      (A j (MaxContactCoverData.derivedTriple S s hftS extra keep)).toSequenceOfBlowups :=
    IsStrictPullbackBlowupSeq.of_eq (eq_of_heq ((A j).toSequenceOfBlowups_heq_of_eq hkey)) rfl h0
  obtain ⟨hmkS, hSeq, -⟩ := appendLowerDimReduction_eq_append hstar hinv T P A B j hspec rc hrc S hV hm hO s
    extra keep hftS hdim hP hVc hj hsep
  obtain ⟨hmkT, hTeq, -⟩ := appendLowerDimReduction_eq_append hstar hinv T P A B j hspec rc hrc (pullbackTriple S g)
    hV' hm' hO' t (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep
    hftT hdim' hP' hVc' hj' hsep'
  rw [hSeq, hTeq]
  refine ⟨(MarkedBlowupSequenceData.isStrictPullbackBlowupSeq_append g s _ t _ hinv D ?_).toStrictPullbackBlowupSeq⟩
  exact (IsStrictPullbackBlowupSeq.of_eq
    (BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups _ _ _ _ _ hmkT).symm
    (BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups _ _ _ _ _ hmkS).symm
    ((hspb.of_isomorphic_pullback (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm).of_isomorphic_base
      (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm)).toStrictPullbackBlowupSeq

end LowerDimReductionPullback

end FunctorialResolution.EmbeddedResolution

end
