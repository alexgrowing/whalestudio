import Formalism.LatticeSlopes.Statement

open Module Submodule

noncomputable section

namespace Formalism.F

def satur {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L N : Submodule ℤ E) :
    Submodule ℤ E :=
  L ⊓ (Submodule.span ℝ (N : Set E)).restrictScalars ℤ

def SlopesBdd : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E), DiscreteTopology L → BddAbove (slopes L)

def CovolAntiSameRank : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (N N' : Submodule ℤ E), DiscreteTopology N' → N ≤ N' → rk N = rk N' → covol N' ≤ covol N

def SaturProps : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L N : Submodule ℤ E), DiscreteTopology L → N ≤ L →
    IsSaturated L (satur L N) ∧ N ≤ satur L N ∧ rk (satur L N) = rk N

def FiniteSaturated : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E), DiscreteTopology L → ∀ X : ℝ,
    {N : Submodule ℤ E | IsSaturated L N ∧ covol N ≤ X}.Finite

def ShortVector : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E), DiscreteTopology L → L ≠ ⊥ →
    ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ ≤ Real.sqrt (rk L : ℝ) * covol L ^ ((1 : ℝ) / (rk L : ℝ))

end Formalism.F
