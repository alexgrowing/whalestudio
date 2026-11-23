import Mathlib

open Matrix

noncomputable section

namespace PI

def ExpTri : Prop :=
  ∀ (n : ℕ) (X Y Z U : Matrix (Fin n) (Fin n) ℂ), Xᴴ = X → Yᴴ = Y → Zᴴ = Z →
    U ∈ Matrix.unitaryGroup (Fin n) ℂ →
    NormedSpace.exp X * NormedSpace.exp Y = U * NormedSpace.exp Z →
    Real.sqrt (∑ i, ∑ j, ‖Z i j‖ ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) + Real.sqrt (∑ i, ∑ j, ‖Y i j‖ ^ 2)

end PI

end
