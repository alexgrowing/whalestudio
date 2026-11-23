import Formalism.ThetaSupremumBounds.StatementB

open Finset

namespace Formalism.DimensionVariation

def ext0 {r : ℕ} (f : Fin r → ℝ) (i : ℕ) : ℝ := if h : i < r then f ⟨i, h⟩ else 0

theorem extendByZeroOnSubset_apply_coe {r : ℕ} (f : Fin r → ℝ) (i : Fin r) : ext0 f (i : ℕ) = f i := by
  simp [ext0, i.2]

end Formalism.DimensionVariation
