import Formalism.SharpRestriction.LevelLetterCocycles.PrimesOverLiterature.RayPrimeCount

namespace Formalism.MainNotions.N.Lit.RayPrimeCountQ

open Formalism.MainNotions.N.Lit.RayLarger Formalism.MainNotions.N.Lit.RayPrimeCount

def Stmt : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ε' < 1 / 4 →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
      ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → 0 < d → 0 < m → 4 * d ∣ m →
        (∃ z ∈ K, z ^ 2 = -(d : Qb)) →
        ∀ Y : ℝ, 1 ≤ Y → C * Real.log (m : ℝ) ^ 2 ≤ Real.log Y →
          Y ^ (1 - ε') ≤ (count K m Y : ℝ)

example : 0 < (1 : ℕ) ∧ 0 < (4 : ℕ) ∧ 4 * 1 ∣ (4 : ℕ) := by decide

end Formalism.MainNotions.N.Lit.RayPrimeCountQ
