import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

open scoped Classical

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

section

variable {X : Scheme.{u}}

def monomialSplitting (E : List X.IdealSheafData) (I : X.IdealSheafData) :
    X.IdealSheafData × X.IdealSheafData :=
  if h : ∃ q : X.IdealSheafData × X.IdealSheafData, IsMonomialSplitting E I q.1 q.2 then
    h.choose
  else (⊤, I)

def monomialPart (E : List X.IdealSheafData) (I : X.IdealSheafData) : X.IdealSheafData :=
  (monomialSplitting E I).1

def nonMonomialPart (E : List X.IdealSheafData) (I : X.IdealSheafData) : X.IdealSheafData :=
  (monomialSplitting E I).2

theorem isMonomialSplitting_monomialPart_nonMonomialPart (E : List X.IdealSheafData) (I : X.IdealSheafData)
    (h : ∃ q : X.IdealSheafData × X.IdealSheafData, IsMonomialSplitting E I q.1 q.2) :
    IsMonomialSplitting E I (monomialPart E I) (nonMonomialPart E I) := by
  unfold monomialPart nonMonomialPart monomialSplitting
  rw [dif_pos h]
  exact h.choose_spec

end

section

variable {X : Scheme.{u}}

def maxOrder (N : X.IdealSheafData) : ℕ :=
  sSup {n : ℕ | ∃ x : ↥X, (n : ℕ∞) ≤ orderAt N x}

def maxOrderOn (N : X.IdealSheafData) (S : Set ↥X) : ℕ :=
  sSup {n : ℕ | ∃ x ∈ S, (n : ℕ∞) ≤ orderAt N x}

end

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def markedDataOfSeq (s : MarkedBlowupSequenceData p I m E) (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (t : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J μ (s.boundary s.length)) :
    Option (MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) :=
  if h : (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m
      (s.boundary s.length) then
    some ((BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).toMarkedBlowupSequenceData (s.proj s.length ≫ p)
      (s.ideal s.length) m (s.boundary s.length) h)
  else
    none

def appendIfMarked (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ)
    (t : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J μ (s.boundary s.length)) :
    MarkedBlowupSequenceData p I m E :=
  match markedDataOfSeq s J μ t with
  | some d => s.append d hinv
  | none => s

end

section

def tripleAtLength (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := s.obj s.length
  structMap := s.proj s.length ≫ T.structMap
  ideal := J
  mult := μ
  boundary := s.boundary s.length

def appendRecursivePrincipalization (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (J : (s.obj s.length).IdealSheafData) (μ : ℕ) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  if h : (tripleAtLength T s J μ).krullDimSucc ≤ T.krullDimSucc then
    appendIfMarked hinv s J μ (rc (tripleAtLength T s J μ) h)
  else s

def nonMonomialOrderReductionIter (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    ℕ → MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
  | 0 => emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
  | n + 1 =>
    if T.mult ≤
          maxOrder (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
            (nonMonomialOrderReductionIter hinv T rc n).length)
            ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length)) ∧
        (orderAtLeastLocus
            (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
              (nonMonomialOrderReductionIter hinv T rc n).length)
              ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length))
            (maxOrder (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
              (nonMonomialOrderReductionIter hinv T rc n).length)
              ((nonMonomialOrderReductionIter hinv T rc n).ideal
                (nonMonomialOrderReductionIter hinv T rc n).length)))).Nonempty then
      appendRecursivePrincipalization hinv T rc (nonMonomialOrderReductionIter hinv T rc n)
        (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
          (nonMonomialOrderReductionIter hinv T rc n).length)
          ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length))
        (maxOrder (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
          (nonMonomialOrderReductionIter hinv T rc n).length)
          ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length)))
    else nonMonomialOrderReductionIter hinv T rc n

def nonMonomialOrderReduction (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  nonMonomialOrderReductionIter hinv T rc (maxOrder (nonMonomialPart T.boundary T.ideal) + 1)

def companionIdealReductionIter (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s₀ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    ℕ → MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
  | 0 => s₀
  | n + 1 =>
    if 1 ≤
        maxOrderOn
          (nonMonomialPart ((companionIdealReductionIter hinv T rc s₀ n).boundary
            (companionIdealReductionIter hinv T rc s₀ n).length)
            ((companionIdealReductionIter hinv T rc s₀ n).ideal (companionIdealReductionIter hinv T rc s₀ n).length))
          (orderAtLeastLocus ((companionIdealReductionIter hinv T rc s₀ n).ideal
            (companionIdealReductionIter hinv T rc s₀ n).length) T.mult) then
      appendRecursivePrincipalization hinv T rc (companionIdealReductionIter hinv T rc s₀ n)
        (nonMonomialPart ((companionIdealReductionIter hinv T rc s₀ n).boundary
            (companionIdealReductionIter hinv T rc s₀ n).length)
            ((companionIdealReductionIter hinv T rc s₀ n).ideal (companionIdealReductionIter hinv T rc s₀ n).length) ^ T.mult ⊔
          (companionIdealReductionIter hinv T rc s₀ n).ideal (companionIdealReductionIter hinv T rc s₀ n).length ^
            maxOrderOn
              (nonMonomialPart ((companionIdealReductionIter hinv T rc s₀ n).boundary
                (companionIdealReductionIter hinv T rc s₀ n).length)
                ((companionIdealReductionIter hinv T rc s₀ n).ideal (companionIdealReductionIter hinv T rc s₀ n).length))
              (orderAtLeastLocus ((companionIdealReductionIter hinv T rc s₀ n).ideal
                (companionIdealReductionIter hinv T rc s₀ n).length) T.mult))
        (T.mult *
          maxOrderOn
            (nonMonomialPart ((companionIdealReductionIter hinv T rc s₀ n).boundary
              (companionIdealReductionIter hinv T rc s₀ n).length)
              ((companionIdealReductionIter hinv T rc s₀ n).ideal (companionIdealReductionIter hinv T rc s₀ n).length))
            (orderAtLeastLocus ((companionIdealReductionIter hinv T rc s₀ n).ideal
              (companionIdealReductionIter hinv T rc s₀ n).length) T.mult))
    else companionIdealReductionIter hinv T rc s₀ n

def companionIdealReduction (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  companionIdealReductionIter hinv T rc (nonMonomialOrderReduction hinv T rc)
    (maxOrderOn
      (nonMonomialPart ((nonMonomialOrderReduction hinv T rc).boundary (nonMonomialOrderReduction hinv T rc).length)
        ((nonMonomialOrderReduction hinv T rc).ideal (nonMonomialOrderReduction hinv T rc).length))
      (orderAtLeastLocus ((nonMonomialOrderReduction hinv T rc).ideal (nonMonomialOrderReduction hinv T rc).length) T.mult) + 1)

def orderReductionData (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary :=
  (companionIdealReduction hinv T rc).append
    (MarkedBlowupSequenceData.ofMarkedSequence
      (monomialPrincipalization hinv
        (tripleAtLength T (companionIdealReduction hinv T rc)
          ((companionIdealReduction hinv T rc).ideal (companionIdealReduction hinv T rc).length) T.mult)))
    hinv

def orderReductionSeq (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (rc : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) : T.SequenceOfBlowups :=
  if orderAtLeastLocus T.ideal T.mult = ∅ then
    emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  else
    (orderReductionData hinv T rc).toMarkedSequenceOfBlowups

end

end FunctorialResolution.EmbeddedResolution

end
