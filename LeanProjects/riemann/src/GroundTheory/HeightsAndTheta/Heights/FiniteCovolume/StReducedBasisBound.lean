import Mathlib

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory

noncomputable section

def ReducedBasisBound.Statement : Prop :=
  ∀ (d : ℕ) (t c : ℝ), 0 < t → ∃ C : ℝ, ∀ (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology L] [IsZLattice ℝ L], (∀ x ∈ L, x ≠ 0 → t ≤ ‖x‖) →
      ZLattice.covolume L ≤ c → ∃ b : Basis (Fin d) ℤ L, ∀ i, ‖(b i : EuclideanSpace ℝ (Fin d))‖ ≤ C

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
