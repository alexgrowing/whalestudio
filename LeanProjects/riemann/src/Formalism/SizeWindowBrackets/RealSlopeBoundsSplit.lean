import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Lattice.Fold

namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas

open Finset

noncomputable section

def wmean {ι : Type*} [Fintype ι] (d X : ι → ℝ) : ℝ :=
  (∑ u, d u * X u) / ∑ u, d u

def umax {ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty X

def sF {ι : Type*} [Fintype ι] (d muN h : ι → ℝ) : ℝ :=
  wmean d (fun u => muN u - h u)

def uF {ι : Type*} [Fintype ι] [Nonempty ι] (d muMaxN muN h : ι → ℝ) : ℝ :=
  umax (fun u => muMaxN u - h u) - sF d muN h

def Slopes2 {ι : Type*} (muMaxN muN muMaxM muM dr BE : ι → ℝ) (Sg0 : ℝ) : Prop :=
  (∀ u, muMaxN u ≤ muMaxM u + (Sg0 - dr u)) ∧ (∀ u, muN u = muM u + (Sg0 - dr u) - BE u)

def Slopes2ge {ι : Type*} (muMaxN muN muMaxM muM dr BE : ι → ℝ) (Sg0 : ℝ) : Prop :=
  (∀ u, muMaxN u ≤ muMaxM u + (Sg0 - dr u)) ∧ (∀ u, muM u + (Sg0 - dr u) - BE u ≤ muN u)

def rhsU {ι : Type*} [Fintype ι] [Nonempty ι] (d muMaxM muM h dr BE : ι → ℝ) : ℝ :=
  umax (fun u => muMaxM u - h u) - wmean d (fun u => muM u - h u) + wmean d (fun u => dr u + BE u)

def LemmaU (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2 muMaxN muN muMaxM muM dr BE Sg0 →
    uF d muMaxN muN h ≤ rhsU d muMaxM muM h dr BE

def LemmaUge (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    uF d muMaxN muN h ≤ rhsU d muMaxM muM h dr BE

def LemmaUNeedsDr : Prop :=
  ¬ ∀ (d muMaxN muN muMaxM muM h dr BE : Unit → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) → Slopes2 muMaxN muN muMaxM muM dr BE Sg0 →
    uF d muMaxN muN h ≤ rhsU d muMaxM muM h dr BE

def LemmaUSharp : Prop :=
  ∃ (d muMaxN muN muMaxM muM h dr BE : Bool → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) ∧ (∀ u, 0 ≤ dr u) ∧ (∀ u, 0 < BE u) ∧ (∃ u, 0 < dr u) ∧
    Slopes2 muMaxN muN muMaxM muM dr BE Sg0 ∧
    uF d muMaxN muN h = rhsU d muMaxM muM h dr BE

def RealSlopeBounds (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 A A' V : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    (∀ u, muMaxM u ≤ A) → (∀ u, -A' ≤ muM u) → (∀ u u', |h u - h u'| ≤ V) →
    uF d muMaxN muN h ≤ A + A' + V + wmean d (fun u => dr u + BE u)

def RealSlopeBoundsSplit (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE lT : ι → ℝ) (Sg0 A A' sa V1 Lk : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    (∀ u, muMaxM u ≤ A) → (∀ u, -A' ≤ muM u) →
    (∀ u u', |(h u + sa * lT u) - (h u' + sa * lT u')| ≤ V1) →
    (∀ u u', |lT u - lT u'| ≤ Lk) →
    uF d muMaxN muN h ≤ A + A' + (V1 + |sa| * Lk) + wmean d (fun u => dr u + BE u)

end

end Formalism.LFunctionChainParameters.WeightedMeanLemmas
