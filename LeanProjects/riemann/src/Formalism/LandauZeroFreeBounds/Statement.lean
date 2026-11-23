import Mathlib

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def InRegion (c : ℝ) (q : ℕ) (s : ℂ) : Prop :=
  1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re

def IsLZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : Prop :=
  (χ ≠ 1 ∨ s ≠ 1) ∧ DirichletCharacter.LFunction χ s = 0

def ZFRDirichlet : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    InRegion c q s → IsLZero χ s →
      χ ^ 2 = 1 ∧ χ ≠ 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
      ∀ (χ' : DirichletCharacter ℂ q) (s' : ℂ), InRegion c q s' → IsLZero χ' s' → χ' = χ ∧ s' = s

end Formalism.ZeroFreeDirichlet
