import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def mixWord {n : ℕ} (a a₀ A' : HermLine ι) (k i : ℕ) : Fin n → HermLine ι :=
  fun j => if (j : ℕ) < i then a else if (j : ℕ) + 1 < k then a₀ else A'

open Classical in

def logRatio (a a₀ : HermLine ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then Real.log (a₀.h z) - Real.log (a.h z) else 0

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
