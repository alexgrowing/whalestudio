import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem list_prod_map_comap {X Y : Scheme.{u}} (q : X ⟶ Y) (Ls : List Y.IdealSheafData) :
    (Ls.map (fun A => A.comap q)).prod = Ls.prod.comap q := by
  induction Ls with
  | nil => simp
  | cons a L ih => simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_mul, ih]

private theorem list_map_comap_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (l : List Z.IdealSheafData) :
    (l.map (fun A => A.comap h)).map (fun A => A.comap g) = l.map (fun A => A.comap (g ≫ h)) := by
  rw [List.map_map]
  refine List.map_congr_left fun A _ => ?_
  simp

private theorem isPullback_projectionToBase_of_index_eq {X Y Z : Scheme.{u}} (b : SequenceOfBlowups X) {i j : ℕ}
    (h : i = j) {σ : Z ⟶ b.schemeAt i} {v : Z ⟶ Y} {g : Y ⟶ X}
    (hp : IsPullback σ v (b.projectionToBase i) g) :
    IsPullback (σ ≫ eqToHom (congrArg (fun n => b.schemeAt n) h)) v (b.projectionToBase j) g := by
  subst h
  simpa using hp

private theorem append_drop_eq_map_comap {X Y : Scheme.{u}} (g : Y ⟶ X)
    (Es Bs : List X.IdealSheafData) (Et Bt : List Y.IdealSheafData) (keep : ℕ)
    (hE : Et = Es.map (fun A => A.comap g)) (hB : Bt = Bs.map (fun A => A.comap g)) :
    Et ++ Bt.drop keep = (Es ++ Bs.drop keep).map (fun A => A.comap g) := by
  subst hE
  subst hB
  rw [List.map_append, List.map_drop]

private theorem markedIdealWithBoundary_mk_eq_of_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of k)) {I I' : X.IdealSheafData} {m m' : ℕ}
    {E E' : List X.IdealSheafData} (hI : I = I') (hm : m = m') (hE : E = E') :
    MarkedIdealWithBoundary.mk k X q I m E = MarkedIdealWithBoundary.mk k X q I' m' E' := by
  subst hI
  subst hm
  subst hE
  rfl

private theorem isStrictPullback_of_morphism_eq {X' X : Scheme.{u}} {g g' : X' ⟶ X} (h : g = g')
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (hd : IsStrictPullbackBlowupSeq g t s) :
    IsStrictPullbackBlowupSeq g' t s := by
  subst h
  exact hd

private theorem isAdmissible_of_eq {T T' : MarkedIdealWithBoundary.{u}} (h : T = T') (hv : T'.IsAdmissible) :
    T.IsAdmissible := by
  subst h
  exact hv

private theorem pred_dim_of_eq (P : ℕ → Prop) {T T' : MarkedIdealWithBoundary.{u}} (h : T = T')
    (hp : P T'.krullDimSucc) : P T.krullDimSucc := by
  subst h
  exact hp

private theorem isOrderBoundedByMult_of_eq {T T' : MarkedIdealWithBoundary.{u}} (h : T = T')
    (ho : T'.IsOrderBoundedByMult) : T.IsOrderBoundedByMult := by
  subst h
  exact ho

private theorem lt_boundary_length_of_eq {T T' : MarkedIdealWithBoundary.{u}} (h : T = T') {j : ℕ}
    (hj : j < T'.boundary.length) : j < T.boundary.length := by
  subst h
  exact hj

private theorem isBalanced_of_eq {T T' : MarkedIdealWithBoundary.{u}} (h : T = T')
    (hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap)
    (hft' : AlgebraicGeometry.LocallyOfFiniteType T'.structMap)
    (hd : T'.IsBalanced hft') : T.IsBalanced hft := by
  subst h
  exact hd

private theorem isStrictPullback_of_markedIdealWithBoundary_eq (A : PrincipalizationAssignment.{u})
    {T T' : MarkedIdealWithBoundary.{u}} (h : T = T')
    {X : Scheme.{u}} {B : SequenceOfBlowups X} {φ : T.scheme ⟶ X} {φ' : T'.scheme ⟶ X} (hφ : HEq φ φ')
    (hd : IsStrictPullbackBlowupSeq φ (A T).toSequenceOfBlowups B) :
    IsStrictPullbackBlowupSeq φ' (A T').toSequenceOfBlowups B := by
  subst h
  cases hφ
  exact hd

private def castStrictPullbackBlowupSeq {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t t' : SequenceOfBlowups X'} {s s' : SequenceOfBlowups X} (ht : t = t') (hs : s = s')
    (D : StrictPullbackBlowupSeq g t s) : StrictPullbackBlowupSeq g t' s' := by
  subst ht
  subst hs
  exact D

private theorem isStrictPullback_of_markedBlowupSequenceData_eq {k k' : Type u} [Field k] [Field k']
    {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} {g : X' ⟶ X}
    {a b : MarkedBlowupSequenceData p I m E} {a' b' : MarkedBlowupSequenceData p' I' m' E'}
    (ha : a = b) (ha' : a' = b')
    (H : IsStrictPullbackBlowupSeq g a'.toMarkedSequenceOfBlowups.toSequenceOfBlowups a.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g b'.toMarkedSequenceOfBlowups.toSequenceOfBlowups b.toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  subst ha
  subst ha'
  exact H

def DerivIdealSheafIterateCommBaseChange : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [CharZero k] [CharZero L] (f : k →+* L)
    (X Y : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of L))
    [AlgebraicGeometry.Smooth pX] [AlgebraicGeometry.LocallyOfFiniteType pX]
    [AlgebraicGeometry.Smooth pY] [AlgebraicGeometry.LocallyOfFiniteType pY]
    (q : Y ⟶ X),
    IsPullback q pY pX (specMapOfFieldHom k L f) →
      ∀ (r : ℕ) (I : X.IdealSheafData),
        derivIdealSheafIterate L pY r (I.comap q) = (derivIdealSheafIterate k pX r I).comap q

theorem balancedTunedSheaf_comap_of_isPullback (hderiv : DerivIdealSheafIterateCommBaseChange.{u})
    (k L : Type u) [Field k] [Field L] [CharZero k] [CharZero L] (f : k →+* L)
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of L))
    [AlgebraicGeometry.Smooth pX] [AlgebraicGeometry.LocallyOfFiniteType pX]
    [AlgebraicGeometry.Smooth pY] [AlgebraicGeometry.LocallyOfFiniteType pY]
    (q : Y ⟶ X) (hq : IsPullback q pY pX (specMapOfFieldHom k L f))
    (I : X.IdealSheafData) (m : ℕ) :
    balancedTunedSheaf L pY (I.comap q) m = (balancedTunedSheaf k pX I m).comap q := by
  rw [balancedTunedSheaf_eq, balancedTunedSheaf_eq, tunedSheaf_eq_iSup, tunedSheaf_eq_iSup, Scheme.IdealSheafData.comap_iSup]
  refine iSup_congr fun c => ?_
  rw [← list_prod_map_comap q, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun r _ => ?_)
  simp [Function.comp_apply, hderiv k L f X Y pX pY q hq r I,
    AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]

namespace MarkedBlowupSequenceData

theorem isStrictPullbackBlowupSeq_append_of_field {k k' : Type u} [Field k] [Field k']
    {X X' : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k')}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m m' : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} (g : X' ⟶ X)
    (s : MarkedBlowupSequenceData p I m E)
    (u : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (s' : MarkedBlowupSequenceData p' I' m' E')
    (u' : MarkedBlowupSequenceData (s'.proj s'.length ≫ p') (s'.ideal s'.length) m'
      (s'.boundary s'.length))
    (hinv : ComapIsoInvariance.{u})
    (D : StrictPullbackBlowupSeq g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap u'.toMarkedSequenceOfBlowups.toSequenceOfBlowups u.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g ((s'.append u' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups)
      ((s.append u hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) :=
  FunctorialResolution.EmbeddedResolution.isStrictPullbackBlowupSeq_append (g := g) s.toBlowupSequenceData u.toBlowupSequenceData s'.toBlowupSequenceData
    u'.toBlowupSequenceData D D'

end MarkedBlowupSequenceData

namespace LowerDimReductionPullback

variable (S : MarkedIdealWithBoundary.{u}) (L : Type u) [Field L] (f : S.base →+* L)
  (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  (t : MarkedBlowupSequenceData (S.baseChange L f).structMap (S.baseChange L f).ideal
      (S.baseChange L f).mult (S.baseChange L f).boundary)

theorem length_eq_of_strictPullbackBlowupSeq
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    t.length = s.length := by
  have h : t.toMarkedSequenceOfBlowups.length = s.toMarkedSequenceOfBlowups.length := D.length_eq
  rw [MarkedBlowupSequenceData.toMarkedSequence_length, MarkedBlowupSequenceData.toMarkedSequence_length] at h
  exact h

noncomputable def baseChangeMapAtLength
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    t.obj t.length ⟶ s.obj s.length :=
  D.lastMap

theorem baseChangeMapAtLength_eq_lastMap
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    baseChangeMapAtLength S L f s t D = D.lastMap := rfl

@[reducible] noncomputable def comapBoundaryBaseChange
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (Ls : List (s.obj s.length).IdealSheafData) : List (t.obj t.length).IdealSheafData :=
  Ls.map (fun A => A.comap (baseChangeMapAtLength S L f s t D))

theorem nonempty_strictPullbackSeq_appendLowerDimReduction_baseChange
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    [CharZero L]
    [AlgebraicGeometry.Flat (pullback.fst S.structMap (specMapOfFieldHom S.base L f))]
    (hderiv : DerivIdealSheafIterateCommBaseChange.{u}) (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u}) (Bp : PrincipalizationAssignment.{u}) (j : ℕ)
    (hspec : IsBoundaryDivisorReduction P j (A j) Bp)
    (T T' : MarkedIdealWithBoundary.{u})
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hftS : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : AlgebraicGeometry.LocallyOfFiniteType
      (t.proj t.length ≫ (S.baseChange L f).structMap))
    (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hNs : ∀ i ≤ s.length, AlgebraicGeometry.IsLocallyNoetherian (s.obj i))
    (hV' : (S.baseChange L f).IsAdmissible)
    (hO' : ∀ x : ↥(S.baseChange L f).scheme,
      orderAt (S.baseChange L f).ideal x ≤ ((S.baseChange L f).mult : ℕ∞))
    (hNt : ∀ i ≤ t.length, AlgebraicGeometry.IsLocallyNoetherian (t.obj i))
    (hdim : (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc ≤ T.krullDimSucc)
    (hP : P (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc)
    (hVc : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsAdmissible)
    (hj : j < (extra ++ (s.boundary s.length).drop keep).length)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take keep,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : Set ↥(s.obj s.length)) = ∅)
    (hdim' : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).krullDimSucc ≤ T'.krullDimSucc)
    (hP' : P (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).krullDimSucc)
    (hVc' : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).IsAdmissible)
    (hj' : j < (@List.append (t.obj t.length).IdealSheafData (comapBoundaryBaseChange S L f s t D extra)
      ((t.boundary t.length).drop keep)).length)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take keep,
      orderAtLeastLocus (t.ideal t.length) (S.baseChange L f).mult ∩
        (Dv.support : Set ↥(t.obj t.length)) = ∅)
    (hVb : ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).IsAdmissible)
    (hPb : P ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).krullDimSucc)
    (hOb : ∀ x : ↥((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).scheme,
      orderAt ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).ideal x ≤
        ((MaxContactCoverData.derivedTriple S s hftS extra keep).mult : ℕ∞))
    (hDb : ∀ hft : AlgebraicGeometry.LocallyOfFiniteType
        ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).structMap,
      ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).IsBalanced hft) :
    Nonempty (StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      (MaxContactReduction.appendLowerDimReduction hinv T' (fun S' _ i => A i S') (S.baseChange L f) t
        (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap)
        keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T (fun S' _ i => A i S') S s extra keep
        j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  classical
  have hlen : t.length = s.length := length_eq_of_strictPullbackBlowupSeq S L f s t D
  have hm' : 1 ≤ (S.baseChange L f).mult := hm
  have hbe : comapBoundaryBaseChange S L f s t D extra = extra.map (fun A => A.comap D.lastMap) := rfl
  obtain ⟨hmk1, heq1, -⟩ :=
    LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A Bp j hspec (fun S' _ i => A i S')
      (fun _ _ _ => rfl) S hV hm hO s extra keep hftS hdim hP hVc hj hsep
  obtain ⟨hmk2, heq2, -⟩ :=
    LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T' P A Bp j hspec (fun S' _ i => A i S')
      (fun _ _ _ => rfl) (S.baseChange L f) hV' hm' hO' t (comapBoundaryBaseChange S L f s t D extra) keep
      hftT hdim' hP' hVc' hj' hsep'
  have hcz : CharZero S.base := hV.charZero
  have hsmA : AlgebraicGeometry.Smooth
      ((s.proj s.length ≫ S.structMap : s.obj s.length ⟶ Spec (CommRingCat.of S.base))) :=
    hVc.smooth
  have hsmB : AlgebraicGeometry.Smooth
      ((t.proj t.length ≫ (S.baseChange L f).structMap :
        t.obj t.length ⟶ Spec (CommRingCat.of L))) :=
    hVc'.smooth
  have hftA : AlgebraicGeometry.LocallyOfFiniteType
      ((s.proj s.length ≫ S.structMap : s.obj s.length ⟶ Spec (CommRingCat.of S.base))) :=
    hftS
  have hftB : AlgebraicGeometry.LocallyOfFiniteType
      ((t.proj t.length ≫ (S.baseChange L f).structMap :
        t.obj t.length ⟶ Spec (CommRingCat.of L))) :=
    hftT
  have hbase : IsPullback (D.comp t.length le_rfl)
      (t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase t.length)
      (s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase t.length)
      (pullback.fst S.structMap (specMapOfFieldHom S.base L f)) :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism
      (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups t.length D.comp D.comp_zero D.pullback
      t.length le_rfl
  have hbase2 := isPullback_projectionToBase_of_index_eq s.toMarkedSequenceOfBlowups.toSequenceOfBlowups hlen hbase
  have hbase3 := hbase2.paste_vert
    (IsPullback.of_hasPullback S.structMap (specMapOfFieldHom S.base L f))
  have e1 : t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase t.length = t.proj t.length :=
    MarkedBlowupSequenceData.toMarkedSequence_projectionToBase t t.length
  have e2 : s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s.length = s.proj s.length :=
    MarkedBlowupSequenceData.toMarkedSequence_projectionToBase s s.length
  have hsq : IsPullback D.lastMap (t.proj t.length ≫ (S.baseChange L f).structMap)
      (s.proj s.length ≫ S.structMap) (specMapOfFieldHom S.base L f) := by
    rw [← e1, ← e2]
    exact hbase3
  have hsq1 : IsPullback D.lastMap (t.proj t.length ≫ (S.baseChange L f).structMap)
      (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap
      (specMapOfFieldHom (MaxContactCoverData.derivedTriple S s hftS extra keep).base L f) := hsq
  obtain ⟨ι, hfst, hsnd⟩ :
      ∃ e : t.obj t.length ≅ pullback (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap
          (specMapOfFieldHom (MaxContactCoverData.derivedTriple S s hftS extra keep).base L f),
        (e.hom ≫ pullback.fst (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap
            (specMapOfFieldHom (MaxContactCoverData.derivedTriple S s hftS extra keep).base L f) = D.lastMap) ∧
          (e.hom ≫ pullback.snd (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap
              (specMapOfFieldHom (MaxContactCoverData.derivedTriple S s hftS extra keep).base L f)
            = t.proj t.length ≫ (S.baseChange L f).structMap) :=
    ⟨hsq1.isoPullback, hsq1.isoPullback_hom_fst, hsq1.isoPullback_hom_snd⟩
  have hisoι : IsIso ι.hom := inferInstance
  have hsmι : AlgebraicGeometry.Smooth ι.hom := inferInstance
  have hsurjι : AlgebraicGeometry.Surjective ι.hom := inferInstance
  have hdiv := (MarkedBlowupSequenceData.isMarked_toBlowupSequenceData s).divisible
  have hpi := MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform (d := s.toBlowupSequenceData) (I := S.ideal) (m := S.mult)
    (E := S.boundary) (g := pullback.fst S.structMap (specMapOfFieldHom S.base L f)) t D hdiv
    t.length le_rfl
  have hpb := MarkedBlowupSequenceData.boundary_eq_comap_strictPullbackComparisonMap (d := s.toBlowupSequenceData) (I := S.ideal) (m := S.mult)
    (E := S.boundary) (g := pullback.fst S.structMap (specMapOfFieldHom S.base L f)) t D hNs hNt
    t.length le_rfl
  have hpm : MarkedBlowupSequenceData.strictPullbackComparisonMap (q := (S.baseChange L f).structMap)
      (g := pullback.fst S.structMap (specMapOfFieldHom S.base L f)) (I := S.ideal) (m := S.mult)
      (E := S.boundary) (d := s.toBlowupSequenceData) t D t.length le_rfl ≫
        eqToHom (congrArg (fun n => s.obj n) hlen) = D.lastMap := rfl
  have hIdealLast : t.ideal t.length = (s.ideal s.length).comap D.lastMap := by
    refine hpi.trans ?_
    rw [MarkedBlowupSequenceData.toBlowupSequenceData_controlledTransform_eq s t.length (le_of_eq hlen),
      MarkedBlowupSequenceData.ideal_congr_index s hlen, ← Scheme.IdealSheafData.comap_comp]
    exact congrArg (fun q => (s.ideal s.length).comap q) hpm
  have hBoundaryLast : t.boundary t.length
      = (s.boundary s.length).map (fun A => A.comap D.lastMap) := by
    refine hpb.trans ?_
    rw [MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq_boundary_of_le s t.length (le_of_eq hlen),
      MarkedBlowupSequenceData.boundary_congr_index s hlen, List.map_map]
    refine List.map_congr_left fun A _ => ?_
    simp only [Function.comp_apply, ← Scheme.IdealSheafData.comap_comp]
    exact congrArg (fun q => A.comap q) hpm
  have htuned := balancedTunedSheaf_comap_of_isPullback hderiv S.base L f
    (s.proj s.length ≫ S.structMap) (t.proj t.length ≫ (S.baseChange L f).structMap)
    D.lastMap hsq (s.ideal s.length) S.mult
  have hid : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
        (comapBoundaryBaseChange S L f s t D extra) keep).ideal
      = ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).ideal.comap ι.hom := by
    have hA : ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).ideal.comap ι.hom
        = (LowerDimReductionPullback.tunedIdealAtLength S s hftS).comap D.lastMap := by
      refine Eq.trans (congrArg (fun I => I.comap ι.hom)
        (MarkedIdealWithBoundary.baseChange_ideal (MaxContactCoverData.derivedTriple S s hftS extra keep) L f)) ?_
      refine Eq.trans (Scheme.IdealSheafData.comap_comp _ _ _).symm ?_
      refine Eq.trans (congrArg
        (fun m => (MaxContactCoverData.derivedTriple S s hftS extra keep).ideal.comap m) hfst) ?_
      exact congrArg (fun I => I.comap D.lastMap)
        (LowerDimReductionPullback.ideal_derivedTriple S s hftS extra keep)
    have hB : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
          (comapBoundaryBaseChange S L f s t D extra) keep).ideal
        = (LowerDimReductionPullback.tunedIdealAtLength S s hftS).comap D.lastMap := by
      rw [LowerDimReductionPullback.ideal_derivedTriple (S.baseChange L f) t hftT (comapBoundaryBaseChange S L f s t D extra) keep,
        LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf (S.baseChange L f) t hftT, LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf S s hftS,
        hIdealLast]
      exact htuned
    exact hB.trans hA.symm
  have hbd : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
        (comapBoundaryBaseChange S L f s t D extra) keep).boundary
      = (((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).boundary).map
          (fun Dv => Dv.comap ι.hom) := by
    have r1 : (((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).boundary).map
          (fun Dv => Dv.comap ι.hom)
        = (extra ++ (s.boundary s.length).drop keep).map (fun A => A.comap D.lastMap) := by
      refine Eq.trans (congrArg (fun l => l.map (fun Dv => Dv.comap ι.hom))
        (MarkedIdealWithBoundary.baseChange_boundary
          (MaxContactCoverData.derivedTriple S s hftS extra keep) L f)) ?_
      refine Eq.trans (list_map_comap_comp ι.hom
        (pullback.fst (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap
          (specMapOfFieldHom (MaxContactCoverData.derivedTriple S s hftS extra keep).base L f))
        (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary) ?_
      refine Eq.trans (congrArg (fun m =>
        (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary.map
          (fun A => A.comap m)) hfst) ?_
      exact congrArg (fun l => l.map (fun A => A.comap D.lastMap))
        (MaxContactCoverData.derivedTriple_boundary S s hftS extra keep)
    have r2 : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
          (comapBoundaryBaseChange S L f s t D extra) keep).boundary
        = (extra ++ (s.boundary s.length).drop keep).map (fun A => A.comap D.lastMap) := by
      refine Eq.trans (MaxContactCoverData.derivedTriple_boundary (S.baseChange L f) t hftT
        (comapBoundaryBaseChange S L f s t D extra) keep) ?_
      exact append_drop_eq_map_comap D.lastMap extra (s.boundary s.length)
        (comapBoundaryBaseChange S L f s t D extra) (t.boundary t.length) keep hbe hBoundaryLast
    exact r2.trans r1.symm
  have hTriple : ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).pullbackAlong
        (t.obj t.length)
        (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
          (comapBoundaryBaseChange S L f s t D extra) keep).structMap ι.hom
      = MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT (comapBoundaryBaseChange S L f s t D extra) keep :=
    markedIdealWithBoundary_mk_eq_of_eq _ hid.symm rfl hbd.symm
  have hft1 : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap := hVc.locallyOfFiniteType
  have hO1 : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  have hD1 : (MaxContactCoverData.derivedTriple S s hftS extra keep).IsBalanced hft1 :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  have hj1 : j < (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary.length :=
    lt_of_lt_of_eq hj (congrArg List.length
      (MaxContactCoverData.derivedTriple_boundary S s hftS extra keep)).symm
  have hO1b : ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr hOb
  have hlenb : ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).boundary.length
      = (MaxContactCoverData.derivedTriple S s hftS extra keep).boundary.length :=
    (congrArg List.length
      (MarkedIdealWithBoundary.baseChange_boundary (MaxContactCoverData.derivedTriple S s hftS extra keep) L f)).trans
      (List.length_map _)
  have hj1b :
      j < ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).boundary.length :=
    lt_of_lt_of_eq hj1 hlenb.symm
  have hbc := hspec.isStrictPullbackBlowupSeq_baseChange (MaxContactCoverData.derivedTriple S s hftS extra keep)
    hVc hP hO1 hD1 hj1 L f hVb hPb hO1b (hDb hVb.locallyOfFiniteType) hj1b
  have hO2 : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar (S.baseChange L f) hV' hm' hO' t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep hVc'
  have hD2b : (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).IsBalanced hVc'.locallyOfFiniteType :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar (S.baseChange L f) hV' hm' hO' t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep hVc'
  have hj2 : j < (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).boundary.length :=
    lt_of_lt_of_eq hj' (congrArg List.length
      (MaxContactCoverData.derivedTriple_boundary (S.baseChange L f) t hftT
        (comapBoundaryBaseChange S L f s t D extra) keep)).symm
  have hStrictPullback := @IsBoundaryDivisorReduction.isStrictPullbackBlowupSeq_of_smooth_surjective P j (A j) Bp hspec
    ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f) hVb hPb hO1b
    (hDb hVb.locallyOfFiniteType) hj1b (t.obj t.length)
    (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).structMap
    ι.hom hsmι hsurjι hsnd
    (isAdmissible_of_eq hTriple hVc') (pred_dim_of_eq P hTriple hP')
    (isOrderBoundedByMult_of_eq hTriple hO2)
    (isBalanced_of_eq hTriple _ _ hD2b)
    (lt_boundary_length_of_eq hTriple hj2)
  have hsmT : IsStrictPullbackBlowupSeq ι.hom
      (A j (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
        (comapBoundaryBaseChange S L f s t D extra) keep)).toSequenceOfBlowups
      (A j ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f)).toSequenceOfBlowups :=
    isStrictPullback_of_markedIdealWithBoundary_eq (A j) hTriple (HEq.refl ι.hom) hStrictPullback
  have hcomp := isStrictPullback_of_morphism_eq hfst (hsmT.comp hbc)
  have hD'0 := (hcomp.of_isomorphic_pullback (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm).of_isomorphic_base
    (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm
  have hE1 := BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups
    (BlowupSequenceData.ofSequenceOfBlowups (A j (MaxContactCoverData.derivedTriple S s hftS extra keep)).toSequenceOfBlowups)
    (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult (s.boundary s.length) hmk1
  have hE2 := BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups
    (BlowupSequenceData.ofSequenceOfBlowups (A j (MaxContactCoverData.derivedTriple (S.baseChange L f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep)).toSequenceOfBlowups)
    (t.proj t.length ≫ (S.baseChange L f).structMap) (t.ideal t.length) (S.baseChange L f).mult
    (t.boundary t.length) hmk2
  have hD2 := castStrictPullbackBlowupSeq hE2.symm hE1.symm hD'0.toStrictPullbackBlowupSeq
  have main := isStrictPullback_of_markedBlowupSequenceData_eq heq1.symm heq2.symm
    (MarkedBlowupSequenceData.isStrictPullbackBlowupSeq_append_of_field
      (pullback.fst S.structMap (specMapOfFieldHom S.base L f)) s _ t _ hinv D hD2)
  exact ⟨main.toStrictPullbackBlowupSeq⟩

end LowerDimReductionPullback

end FunctorialResolution.EmbeddedResolution

end
