import Mathlib

open scoped commutatorElement Pointwise

namespace GlobalTheory

theorem normal_of_commutator_le {G : Type} [Group G] (M : Subgroup G)
    (h : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ M) : M.Normal := by
  constructor
  intro n hn g
  have h1 : ⁅g, n⁆ ∈ M :=
    h (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
  have h2 := M.mul_mem h1 hn
  simpa [commutatorElement_def] using h2

end GlobalTheory

namespace GlobalTheory

end GlobalTheory
