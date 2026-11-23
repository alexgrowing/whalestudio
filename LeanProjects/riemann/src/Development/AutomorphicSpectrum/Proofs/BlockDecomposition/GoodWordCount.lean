import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.GoodWords

variable {N s : ℕ}

open Classical in

noncomputable def leftSet (b β : Fin N → Fin s) (k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x => ∃ i : Fin N, (i : ℕ) < k ∧ β i = b x

def rank (S : Finset (Fin N)) (b : Fin N → Fin s) (x : Fin N) : ℕ :=
  (open Classical in if x ∈ S then 0 else s) + (s - 1 - (b x : ℕ))

end GlobalTheory.CompanionTheory.GoodWords
