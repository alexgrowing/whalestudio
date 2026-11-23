import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def Gap3 (ε : Fin n → Bool) (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∃ h : ℝ, GapAtLeast ε lam h ∧ (n : ℝ) - 1 < h

def BlockAnti (ε : Fin n → Bool) (lam : Fin n → ℝ) : Prop :=
  ∀ a b : Fin n, a < b → ε a = ε b → 1 ≤ lam a - lam b

def IsPosNC (ε : Fin n → Bool) (Ph : Finset (Fin n × Fin n)) : Prop :=
  ∀ x ∈ Ph, x.1 < x.2 ∧ ε x.1 ≠ ε x.2

def phSum (Ph : Finset (Fin n × Fin n)) : Fin n → ℝ := ∑ x ∈ Ph, root x.1 x.2

end ReciprocityTheory.ChartRestriction.DS.TRGap
