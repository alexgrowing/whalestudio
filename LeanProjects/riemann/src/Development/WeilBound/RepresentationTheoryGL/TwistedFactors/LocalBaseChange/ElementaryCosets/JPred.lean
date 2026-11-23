import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel

namespace PositivityTheory.Lbc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def JPred (N m : ℕ) (K : Fin N → Subgroup kˣ) (g : GL (Fin N) k) : Prop :=
  (∀ i, ∃ x ∈ K i, (g : Matrix (Fin N) (Fin N) k) i i = x) ∧
    ∀ i j, i ≠ j → valuation k ((g : Matrix (Fin N) (Fin N) k) i j) ≤ uniformizer k ^ m

variable (k) in

def KHyp (N m : ℕ) (K : Fin N → Subgroup kˣ) : Prop :=
  1 ≤ m ∧ (∀ i, IsOpen (K i : Set kˣ)) ∧ (∀ i, ∀ x ∈ K i, valuation k (x : k) = 1) ∧
    ∀ i (x : kˣ), valuation k ((x : k) - 1) ≤ uniformizer k ^ (2 * m) → x ∈ K i

end PositivityTheory.Lbc

end
