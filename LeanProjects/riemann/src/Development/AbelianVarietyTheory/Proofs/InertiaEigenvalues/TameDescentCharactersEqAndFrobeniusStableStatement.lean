import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentCharactersEqAndFrobeniusStable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open GlobalTheory.BK PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameDescent_characters_eq_and_frobenius_stable : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P), (∀ τ σ, Δ.chars τ = Δ.chars σ) ∧ ∀ τ, ∀ c ∈ Δ.chars τ, (l : ZMod e) * c ∈ Δ.chars τ := by
  first | exact @GlobalTheory.BK.chars_eq_and_mul_mem | exact GlobalTheory.BK.chars_eq_and_mul_mem | (intros; apply GlobalTheory.BK.chars_eq_and_mul_mem <;> assumption)
