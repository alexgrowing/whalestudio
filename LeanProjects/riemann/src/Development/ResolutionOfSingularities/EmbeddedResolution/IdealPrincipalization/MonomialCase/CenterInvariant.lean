import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

def sortedIndices {n : ℕ} (J : Finset (Fin n)) : List ℕ :=
  (J.sort (· ≤ ·)).map Fin.val

theorem sortedIndices_eq_map_sort {n : ℕ} (J : Finset (Fin n)) :
    sortedIndices J = (J.sort (· ≤ ·)).map Fin.val := rfl

theorem mem_sortedIndices {n : ℕ} (J : Finset (Fin n)) (a : ℕ) :
    a ∈ sortedIndices J ↔ ∃ j ∈ J, (j : ℕ) = a := by
  simp [sortedIndices, List.mem_map, Finset.mem_sort]

structure CenterInvariant (n : ℕ) : Type where
  positions : Finset (Fin n)
  rank : ℕ
  value : ℕ∞

def CenterInvariant.sortedIndices {n : ℕ} (K : CenterInvariant n) : List ℕ :=
  _root_.FunctorialResolution.EmbeddedResolution.MonomialCenter.sortedIndices K.positions

def CenterInvariant.Lt {n n' : ℕ} (K : CenterInvariant n) (K' : CenterInvariant n') : Prop :=
  K.rank < K'.rank ∨
    (K.rank = K'.rank ∧
      (K'.value < K.value ∨
        (K.value = K'.value ∧
          List.Lex (· < ·) K.sortedIndices K'.sortedIndices)))

def CenterInvariant.Le {n n' : ℕ} (K : CenterInvariant n) (K' : CenterInvariant n') : Prop :=
  K.Lt K' ∨
    (K.rank = K'.rank ∧ K.value = K'.value ∧ K.sortedIndices = K'.sortedIndices)

def centerInvariant {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) :
    CenterInvariant L.length where
  positions := lexMaxIndices I m L
  rank := minIndexCard I m L
  value := maxCandidateOrder I m L

@[simp] theorem centerInvariant_indices {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : (centerInvariant I m L).positions = lexMaxIndices I m L := rfl

@[simp] theorem centerInvariant_depth {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : (centerInvariant I m L).rank = minIndexCard I m L := rfl

@[simp] theorem centerInvariant_order {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : (centerInvariant I m L).value = maxCandidateOrder I m L := rfl

@[simp] theorem centerInvariant_sortedIndices {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    (centerInvariant I m L).sortedIndices = sortedIndices (lexMaxIndices I m L) := rfl

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
