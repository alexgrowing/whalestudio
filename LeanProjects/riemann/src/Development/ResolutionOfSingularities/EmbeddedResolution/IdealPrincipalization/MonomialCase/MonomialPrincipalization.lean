import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

section

variable {Y : Scheme.{u}}

def intersectionIdeal (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) : Y.IdealSheafData :=
  ⨆ j ∈ J, L.get j

@[simp]
theorem intersectionIdeal_eq_iSup (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) :
    intersectionIdeal L J = ⨆ j ∈ J, L.get j := rfl

def intersectionComponents (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) : Set (Set ↥Y) :=
  {C | IsIrreducible C ∧ C ⊆ ((intersectionIdeal L J).support : Set ↥Y) ∧
    ∀ C' : Set ↥Y, IsIrreducible C' → C ⊆ C' → C' ⊆ ((intersectionIdeal L J).support : Set ↥Y) → C' = C}

open Classical in
def orderAlong (I : Y.IdealSheafData) (C : Set ↥Y) : ℕ∞ :=
  if h : IsIrreducible C then orderAt I h.genericPoint else 0

def IsCandidateComponent (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) (r : ℕ)
    (J : Finset (Fin L.length)) (C : Set ↥Y) : Prop :=
  J.card = r ∧ C ∈ intersectionComponents L J ∧ (m : ℕ∞) ≤ orderAlong I C

def minIndexCard (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) : ℕ :=
  sInf {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y), IsCandidateComponent I m L r J C}

def maxCandidateOrder (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) : ℕ∞ :=
  ⨆ (J : Finset (Fin L.length)) (C : Set ↥Y)
    (_ : IsCandidateComponent I m L (minIndexCard I m L) J C), orderAlong I C

def IsMaxOrderIndexSet (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) : Prop :=
  ∃ C : Set ↥Y, IsCandidateComponent I m L (minIndexCard I m L) J C ∧ orderAlong I C = maxCandidateOrder I m L

def binaryEncode {n : ℕ} (J : Finset (Fin n)) : ℕ :=
  ∑ j ∈ J, 2 ^ (n - 1 - (j : ℕ))

def maxBinaryCode (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) : ℕ :=
  sSup {c : ℕ | ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧ binaryEncode J = c}

open Classical in
def lexMaxIndices (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) :
    Finset (Fin L.length) :=
  if h : ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧ binaryEncode J = maxBinaryCode I m L then
    h.choose
  else ∅

def monomialCenterSet (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) : Set ↥Y :=
  ⋃₀ {C : Set ↥Y |
    IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧ orderAlong I C = maxCandidateOrder I m L}

def openSublocusIdeal {V : Scheme.{u}} (ι : V ⟶ Y) (S : Set ↥V) (hS : IsOpen S) : Y.IdealSheafData :=
  AlgebraicGeometry.Scheme.Hom.ker
    (AlgebraicGeometry.Scheme.Opens.ι (X := V) ⟨S, hS⟩ ≫ ι)

open Classical in
def monomialCenter (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) : Y.IdealSheafData :=
  if h : minIndexCard I m L ≠ 0 ∧
      IsOpen (⇑(intersectionIdeal L (lexMaxIndices I m L)).subschemeι.base ⁻¹' monomialCenterSet I m L) then
    openSublocusIdeal (intersectionIdeal L (lexMaxIndices I m L)).subschemeι
      (⇑(intersectionIdeal L (lexMaxIndices I m L)).subschemeι.base ⁻¹' monomialCenterSet I m L) h.2
  else ⊤

end

namespace MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def centerAtLast (d : MarkedBlowupSequenceData p I m E) : (d.obj d.length).IdealSheafData :=
  monomialCenter (d.ideal d.length) m (d.boundary d.length)

def IsAdmissibleCenter (d : MarkedBlowupSequenceData p I m E) : Prop :=
  centerAtLast d ≠ ⊤ ∧
  AlgebraicGeometry.Smooth ((centerAtLast d).subschemeι ≫ d.proj d.length ≫ p) ∧
  HasStrictNormalCrossingsWith (d.proj d.length ≫ p) (centerAtLast d) (d.boundary d.length) ∧
  (((centerAtLast d).support : Set ↥(d.obj d.length)) ⊆ orderAtLeastLocus (d.ideal d.length) m) ∧
  (∃ B : (Blowup.blowup (centerAtLast d)).IdealSheafData,
    ((centerAtLast d).comap (Blowup.blowup.proj (centerAtLast d))) ^ m * B =
      (d.ideal d.length).comap (Blowup.blowup.proj (centerAtLast d)))

open Classical in
def blowupAtCenter (hinv : ComapIsoInvariance.{u}) (d : MarkedBlowupSequenceData p I m E) :
    MarkedBlowupSequenceData p I m E :=
  if h : IsAdmissibleCenter d then
    d.append
      (ofSingleBlowup (d.proj d.length ≫ p) (d.ideal d.length) m (d.boundary d.length)
        (centerAtLast d) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) hinv
  else d

def monomialBlowupIterate (hinv : ComapIsoInvariance.{u}) (d : MarkedBlowupSequenceData p I m E) :
    ℕ → MarkedBlowupSequenceData p I m E
  | 0 => d
  | (n + 1) => blowupAtCenter hinv (monomialBlowupIterate hinv d n)

theorem monomialBlowupIterate_zero (hinv : ComapIsoInvariance.{u}) (d : MarkedBlowupSequenceData p I m E) :
    monomialBlowupIterate hinv d 0 = d := rfl

theorem monomialBlowupIterate_succ (hinv : ComapIsoInvariance.{u}) (d : MarkedBlowupSequenceData p I m E) (n : ℕ) :
    monomialBlowupIterate hinv d (n + 1) = blowupAtCenter hinv (monomialBlowupIterate hinv d n) := rfl

def IsStationaryAt (hinv : ComapIsoInvariance.{u}) (d : MarkedBlowupSequenceData p I m E) (n : ℕ) : Prop :=
  (monomialBlowupIterate hinv d (n + 1)).length = (monomialBlowupIterate hinv d n).length

end

end MarkedBlowupSequenceData

section

variable {k : Type u} [Field k] {X : Scheme.{u}}

def monomialBlowupSeq (hinv : ComapIsoInvariance.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) : MarkedBlowupSequenceData p I m E :=
  MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
    (sInf {n : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n})

end

def monomialPrincipalization (hinv : ComapIsoInvariance.{u}) : PrincipalizationAssignment.{u} :=
  fun T => (monomialBlowupSeq hinv T.structMap T.ideal T.mult T.boundary).toMarkedSequenceOfBlowups

theorem monomialPrincipalization_apply (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) :
    monomialPrincipalization hinv T =
      (monomialBlowupSeq hinv T.structMap T.ideal T.mult T.boundary).toMarkedSequenceOfBlowups := rfl

end FunctorialResolution.EmbeddedResolution

end
