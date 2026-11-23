import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

open ValuativeRel

noncomputable section

namespace GlobalTheory.UnfoldLoss

open GlobalTheory.SplitFlip GlobalTheory.FunObj

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def varLat (G : Grid k) (ϖ : kˣ) (n : ℕ) : AddSubgroup (Vars G) where
  carrier := {e | ∀ j r, valuation k (e j r) ≤ valuation k ((ϖ ^ n : kˣ) : k)}
  zero_mem' := fun j r => by
    show valuation k 0 ≤ _
    simp
  add_mem' := fun {a b} ha hb j r => (Valuation.map_add _ _ _).trans (max_le (ha j r) (hb j r))
  neg_mem' := fun {a} ha j r => by
    show valuation k (-(a j r)) ≤ _
    rw [Valuation.map_neg]
    exact ha j r

def varCount (G : Grid k) : ℕ :=
  ∑ j : Fin (G.m - 1), Nat.card (StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)))

end GlobalTheory.UnfoldLoss
