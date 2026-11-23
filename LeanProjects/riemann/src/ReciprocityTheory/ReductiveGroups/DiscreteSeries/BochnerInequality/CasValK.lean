import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def layer (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) :
    ℕ → Submodule ℂ M
  | 0 => V
  | k + 1 => layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b)

end Alg

def IsNCSum (ε : Fin n → Bool) (k : ℕ) (ν : Fin n → ℝ) : Prop :=
  ∃ γ : Fin k → Fin n × Fin n, (∀ i, ε (γ i).1 ≠ ε (γ i).2) ∧ ν = ∑ i, root (γ i).1 (γ i).2

def casValK (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := nsq (μ + rhoC ε) - nsq (rhoC ε)

end ReciprocityTheory.ChartRestriction.DS
