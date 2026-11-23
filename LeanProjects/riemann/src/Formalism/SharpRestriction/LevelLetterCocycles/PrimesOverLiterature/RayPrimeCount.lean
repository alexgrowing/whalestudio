import Formalism.SharpRestriction.LevelLetterCocycles.PrimesOverLiterature.RayLarger

namespace Formalism.MainNotions.N.Lit.RayPrimeCount

open Formalism.MainNotions.N.Lit.RayLarger

noncomputable def count (K : Fld) (m : ℕ) (Y : ℝ) : ℕ :=
  Nat.card {p : ℕ // IsRayPrime K m p ∧ Y ≤ p ∧ (p : ℝ) ≤ 2 * Y}

def Stmt : Prop :=
  ∃ C'' C' : ℝ, ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → 0 < d → 0 < m → 4 * d ∣ m →
    (∃ z ∈ K, z ^ 2 = -(d : Qb)) →
    ∀ X : ℝ, (m : ℝ) ^ (C'' + C') ≤ X →
      ∃ Y : ℝ, X * (m : ℝ) ^ (-C') ≤ Y ∧ Y ≤ X ∧ Y * (m : ℝ) ^ (-C'') / Real.log Y ≤ (count K m Y : ℝ)

end Formalism.MainNotions.N.Lit.RayPrimeCount
