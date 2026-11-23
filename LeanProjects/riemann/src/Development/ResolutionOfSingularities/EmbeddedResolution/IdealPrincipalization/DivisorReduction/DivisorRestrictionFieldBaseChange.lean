import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemoval
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

def StrictPullbackFieldBaseChangeOfDimLT (n : ℕ) (L : PrincipalizationAssignment.{u}) : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.krullDimSucc < n →
    ∀ (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
      ((T.baseChange K f).withBoundary E').IsAdmissible →
      ((T.baseChange K f).withBoundary E').krullDimSucc < n →
      IsStrictPullbackBlowupSeq (fieldBaseChangeProjection T K f)
        (L ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups (L T).toSequenceOfBlowups

def StrictPullbackSmoothSurjectiveOfDimLT (n : ℕ) (L : PrincipalizationAssignment.{u}) : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.krullDimSucc < n →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Surjective h],
      h ≫ T.structMap = q →
      ∀ (E' : List Y.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
        ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc < n →
        IsStrictPullbackBlowupSeq h
          (L ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups (L T).toSequenceOfBlowups

theorem strictPullbackFieldBaseChangeOfDimLT_of_isMaxOrderReduction (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) : StrictPullbackFieldBaseChangeOfDimLT n L :=
  hL.base_change_strict

theorem strictPullbackSmoothSurjectiveOfDimLT_of_isMaxOrderReduction (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) : StrictPullbackSmoothSurjectiveOfDimLT n L :=
  hL.smooth_pullback_strict

private theorem toSequenceOfBlowups_heq_of_eq (L : PrincipalizationAssignment.{u}) {A B : MarkedIdealWithBoundary.{u}} (h : A = B) :
    HEq (L A).toSequenceOfBlowups (L B).toSequenceOfBlowups := by
  subst h; rfl

structure DivisorRestrictionFieldBaseChange : Prop where
  comap_comap :
    ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (I : Z.IdealSheafData),
      (I.comap g).comap f = I.comap (f ≫ g)
  comap_baseChangeFieldProj_ne_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K)
      (I : T.scheme.IdealSheafData), I ≠ ⊤ → I.comap (fieldBaseChangeProjection T K f) ≠ ⊤
  lowerTriple_baseChange_comparison :
    ∀ (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K]
      [CharZero K] (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData)
      (hjE : j < E'.length)
      (hD : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f))
      (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
      (I₀' : (T.baseChange K f).scheme.IdealSheafData)
      (E₀' : List (T.baseChange K f).scheme.IdealSheafData)
      (_hI : I₀' = I₀.comap (fieldBaseChangeProjection T K f))
      (_hE : MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.take (E'.length - 1) (E₀'.eraseIdx j))
        (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
          (List.take (T.boundary.length - 1) (E₀.eraseIdx j)))),
      ∃ (E'' : List ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).scheme.IdealSheafData)
        (e : (E'.get ⟨j, hjE⟩).subscheme ⟶ ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).scheme)
        (_ : AlgebraicGeometry.Smooth e) (_ : AlgebraicGeometry.Surjective e),
        MarkedIdealWithBoundary.SameNontrivialBoundary ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).boundary E'' ∧
        e ≫ fieldBaseChangeProjection (restrictToBoundaryDivisor T j hj I₀ E₀) K f =
          divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
            (E'.get ⟨j, hjE⟩) hD ∧
        e ≫ (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').structMap =
          (E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap ∧
        MarkedIdealWithBoundary.SameNontrivialBoundary
          (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
            (List.take (E'.length - 1) (E₀'.eraseIdx j)))
          (List.map (fun D => D.comap e) E'') ∧
        (((T.baseChange K f).withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme
              ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
              (I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι)
              (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
                (List.take (E'.length - 1) (E₀'.eraseIdx j)))).IsAdmissible →
          (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').IsAdmissible) ∧
        (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').krullDimSucc =
          ((T.baseChange K f).withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme
              ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
              (I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι)
              (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
                (List.take (E'.length - 1) (E₀'.eraseIdx j)))).krullDimSucc
  lowerIdealTop_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData),
      lowerIdealWithoutBlowup ((T.baseChange K f).withBoundary E') =
        (lowerIdealWithoutBlowup T).comap (fieldBaseChangeProjection T K f)
  restrictedBoundaryEmptyCenter_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (_hj : j < T.boundary.length) (K : Type u) [Field K]
      [CharZero K] (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
      List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
      j < E'.length →
      MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.take (E'.length - 1)
          ((lowerBoundaryWithoutBlowup ((T.baseChange K f).withBoundary E')).eraseIdx j))
        (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
          (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)))
  lowerIdealPre_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.IsOrderBoundedByMult →
      ∀ (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K]
        (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
        ∀ (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
          ((T.baseChange K f).withBoundary E').IsAdmissible →
          containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
            (containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) →
          lowerIdealAfterBlowup ((T.baseChange K f).withBoundary E') j hjE =
            (lowerIdealAfterBlowup T j hj).comap (fieldBaseChangeProjection T K f)
  restrictedBoundary_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.IsOrderBoundedByMult →
      ∀ (j : ℕ) (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K]
        (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
        ∀ (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
          ((T.baseChange K f).withBoundary E').IsAdmissible →
          containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
            (containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) →
          MarkedIdealWithBoundary.SameNontrivialBoundary
            (List.take (E'.length - 1)
              ((lowerBoundaryAfterBlowup ((T.baseChange K f).withBoundary E') j hjE).eraseIdx j))
            (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
              (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)))

private theorem restrictToBoundaryDivisor_isStrictPullbackBlowupSeq_baseChange (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hflf : DivisorRestrictionFieldBaseChange.{u}) (n : ℕ) (L : PrincipalizationAssignment.{u})
    (hfe : StrictPullbackFieldBaseChangeOfDimLT n L) (hsm : StrictPullbackSmoothSurjectiveOfDimLT n L) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (hj : j < T.boundary.length) (hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty)
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
    (hjE : j < E'.length)
    (hcs' : (orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal T.mult).Nonempty)
    (hD : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f))
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (I₀' : (T.baseChange K f).scheme.IdealSheafData)
    (E₀' : List (T.baseChange K f).scheme.IdealSheafData)
    (hI : I₀' = I₀.comap (fieldBaseChangeProjection T K f))
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.take (E'.length - 1) (E₀'.eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) (E₀.eraseIdx j))))
    (hvT : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible)
    (hvS : (restrictToBoundaryDivisor ((T.baseChange K f).withBoundary E') j hjE I₀' E₀').IsAdmissible) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
        (E'.get ⟨j, hjE⟩) hD)
      (L (restrictToBoundaryDivisor ((T.baseChange K f).withBoundary E') j hjE I₀' E₀')).toSequenceOfBlowups
      (L (restrictToBoundaryDivisor T j hj I₀ E₀)).toSequenceOfBlowups := by
  obtain ⟨E'', e, hsme, hsue, ha, hb, hc, hdbe, heV, hfd⟩ :=
    hflf.lowerTriple_baseChange_comparison T j hj K f E' hjE hD I₀ E₀ I₀' E₀' hI hE
  have hMV : (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').IsAdmissible := heV hvS
  have hMd : (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').krullDimSucc < n := by
    rw [hfd]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt ((T.baseChange K f).withBoundary E') hV' hcs' j hjE I₀' E₀')
      hdim'
  have hdimT : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < n :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj I₀ E₀) hdim
  have h1 := hfe (restrictToBoundaryDivisor T j hj I₀ E₀) hvT hdimT K f E'' ha hMV hMd
  have hsq : divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
        (E'.get ⟨j, hjE⟩) hD ≫ (T.boundary.get ⟨j, hj⟩).subschemeι
      = (E'.get ⟨j, hjE⟩).subschemeι ≫ fieldBaseChangeProjection T K f :=
    subschemeMapOfComap_comp (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hD
  have hid : (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').ideal.comap e
      = I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι := by
    have k1 := hflf.comap_comap _ _ _ e
      (fieldBaseChangeProjection (restrictToBoundaryDivisor T j hj I₀ E₀) K f)
      (I₀.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
    have k2 := congrArg
      (fun (φ : (E'.get ⟨j, hjE⟩).subscheme ⟶ (restrictToBoundaryDivisor T j hj I₀ E₀).scheme) =>
        (I₀.comap (T.boundary.get ⟨j, hj⟩).subschemeι).comap φ) hb
    have k3 := hflf.comap_comap _ _ _
      (divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
        (E'.get ⟨j, hjE⟩) hD)
      (T.boundary.get ⟨j, hj⟩).subschemeι I₀
    have k4 := congrArg
      (fun (φ : (E'.get ⟨j, hjE⟩).subscheme ⟶ T.scheme) => I₀.comap φ) hsq
    have k5 := hflf.comap_comap _ _ _ (E'.get ⟨j, hjE⟩).subschemeι
      (fieldBaseChangeProjection T K f) I₀
    have k6 := congrArg
      (fun (I : (T.baseChange K f).scheme.IdealSheafData) =>
        I.comap (E'.get ⟨j, hjE⟩).subschemeι) hI
    exact k1.trans (k2.trans (k3.trans (k4.trans (k5.symm.trans k6.symm))))
  have htriple : ((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j)))
      = restrictToBoundaryDivisor ((T.baseChange K f).withBoundary E') j hjE I₀' E₀' :=
    congrArg (fun I => (T.baseChange K f).withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) I
        (List.map (fun (D : (T.baseChange K f).scheme.IdealSheafData) =>
            D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j)))) hid
  have hbe : MarkedIdealWithBoundary.SameNontrivialBoundary
      ((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).boundary
      (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
        (List.take (E'.length - 1) (E₀'.eraseIdx j))) := hdbe.symm
  have hva : (((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j)))).IsAdmissible := by
    rw [htriple]; exact hvS
  have hdd : (((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j)))).krullDimSucc < n := by
    rw [htriple]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt ((T.baseChange K f).withBoundary E') hV' hcs' j hjE I₀' E₀')
      hdim'
  have h2 := @hsm (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'') hMV hMd
      (E'.get ⟨j, hjE⟩).subscheme
      ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e hsme hsue hc
      (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
        (List.take (E'.length - 1) (E₀'.eraseIdx j))) hbe hva hdd
  have h4 : IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
        (E'.get ⟨j, hjE⟩) hD)
      (L (((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
          (E'.get ⟨j, hjE⟩).subscheme
          ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).withBoundary
          (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
            (List.take (E'.length - 1) (E₀'.eraseIdx j))))).toSequenceOfBlowups
      (L (restrictToBoundaryDivisor T j hj I₀ E₀)).toSequenceOfBlowups := by
    rw [← hb]
    exact h2.comp h1
  have hLe : (L (((((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').pullbackAlong
        (E'.get ⟨j, hjE⟩).subscheme
        ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) e).withBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j))))).toSequenceOfBlowups
      = (L (restrictToBoundaryDivisor ((T.baseChange K f).withBoundary E') j hjE I₀' E₀')).toSequenceOfBlowups :=
    eq_of_heq (toSequenceOfBlowups_heq_of_eq L htriple)
  exact (congrArg (fun t : SequenceOfBlowups (E'.get ⟨j, hjE⟩).subscheme =>
      IsStrictPullbackBlowupSeq
        (divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
          (E'.get ⟨j, hjE⟩) hD) t (L (restrictToBoundaryDivisor T j hj I₀ E₀)).toSequenceOfBlowups) hLe).mp h4

theorem restrictedFieldBaseChange_of_strictPullback (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hflf : DivisorRestrictionFieldBaseChange.{u}) (n : ℕ) (L : PrincipalizationAssignment.{u})
    (hfe : StrictPullbackFieldBaseChangeOfDimLT n L) (hsm : StrictPullbackSmoothSurjectiveOfDimLT n L) (j : ℕ) :
    RestrictedPrincipalizationFieldBaseChange n L j := by
  constructor
  · intro T hV hdim hO hbal hj hcs K instK instC f E' hBE htake hV' hdim' hO' hDB' hjE hcs'
      hZ hZ'
    exact restrictToBoundaryDivisor_isStrictPullbackBlowupSeq_baseChange hres hfacts hflf n L hfe hsm j T hV hdim hj hcs K f E' hV' hdim'
      hjE hcs' (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake)
      (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
      (lowerIdealWithoutBlowup ((T.baseChange K f).withBoundary E'))
      (lowerBoundaryWithoutBlowup ((T.baseChange K f).withBoundary E'))
      (hflf.lowerIdealTop_baseChange T K f E')
      (hflf.restrictedBoundaryEmptyCenter_baseChange T j hj K f E' hBE htake hjE)
      (hfacts.valid_lowerTop T hV hO hbal j hj hZ)
      (hfacts.valid_lowerTop ((T.baseChange K f).withBoundary E') hV' hO' hDB' j hjE hZ')
  · intro T hV hdim hO hbal hj hcs K instK instC f E' hBE htake hV' hdim' hO' hDB' hjE hcs'
      hZ hZ'
    have hZ2 : containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE ≠ ⊤ := by
      rw [hZ']
      exact hflf.comap_baseChangeFieldProj_ne_top T K f (containedComponentsIdeal T j hj) hZ
    exact restrictToBoundaryDivisor_isStrictPullbackBlowupSeq_baseChange hres hfacts hflf n L hfe hsm j T hV hdim hj hcs K f E' hV' hdim'
      hjE hcs' (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake)
      (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
      (lowerIdealAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
      (lowerBoundaryAfterBlowup ((T.baseChange K f).withBoundary E') j hjE)
      (hflf.lowerIdealPre_baseChange T hV hO j hj K f E' hBE hjE htake hV' hZ')
      (hflf.restrictedBoundary_baseChange T hV hO j hj K f E' hBE hjE htake hV' hZ')
      (hfacts.valid_lowerPre T hV hO hbal j hj hZ)
      (hfacts.valid_lowerPre ((T.baseChange K f).withBoundary E') hV' hO' hDB' j hjE hZ2)

theorem divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange_of_isMaxOrderReduction
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hfbc : FieldBaseChangeCompatibility.{u})
    (hflf : DivisorRestrictionFieldBaseChange.{u}) (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ)
    (hshape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsStrictPullbackBlowupSeq (fieldBaseChangeProjection T K f)
      (((canonicalAlgorithmRules hres).divisorFamily L j ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) :=
  divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange hres hfacts hbc hfbc n L j
    (restrictedFieldBaseChange_of_strictPullback hres hfacts hflf n L
      (strictPullbackFieldBaseChangeOfDimLT_of_isMaxOrderReduction n L O hL)
      (strictPullbackSmoothSurjectiveOfDimLT_of_isMaxOrderReduction n L O hL) j)
    hshape T hV hdim hO hbal hj K f E' hBE htake hV' hdim' hO' hDB' hjE

theorem divisorFamily_isPullbackBlowupSequence_fieldBaseChange_of_isMaxOrderReduction
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hfbc : FieldBaseChangeCompatibility.{u})
    (hflf : DivisorRestrictionFieldBaseChange.{u}) (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ)
    (hshape : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsPullbackBlowupSequence (fieldBaseChangeProjection T K f)
      (((canonicalAlgorithmRules hres).divisorFamily L j ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) :=
  divisorFamily_isPullbackSequenceOfBlowups_fieldBaseChange hres hfacts hbc hfbc n L j
    (restrictedFieldBaseChange_of_strictPullback hres hfacts hflf n L
      (strictPullbackFieldBaseChangeOfDimLT_of_isMaxOrderReduction n L O hL)
      (strictPullbackSmoothSurjectiveOfDimLT_of_isMaxOrderReduction n L O hL) j)
    hshape
    (fun S hS hdS hboundS hDS hjS i hi =>
      divisorFamily_canonicalAlgorithmRules_center_nonempty hres hfacts n L O hL j S hS hdS hboundS hDS hjS i hi)
    (fun _Y s hs => SequenceOfBlowups.withoutIsoBlowups_isomorphic_self s hs)
    T hV hdim hO hbal hj K f E' hBE htake hV' hdim' hO' hDB' hjE

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
