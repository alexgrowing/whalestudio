import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExactTripleJumpsCharactersLift
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_exactTriple_jumps_characters_lift : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (D₂ : BKDat O K l e a μ η H) (F : BKHom D₀ D₁) (G : BKHom D₁ D₂), IsExactTriple F.toHom G.toHom → D₀.jumps ⊆ D₁.jumps ∧ (∀ τ, D₀.desc.chars τ ⊆ D₁.desc.chars τ) ∧ Function.Injective F.onPol ∧ (∀ n : ℕ, (∀ y ∈ D₂.M, ∃ x ∈ D₁.M, G.app x = (l : K) ^ n • y) → ∀ w ∈ D₁.Z, G.onPol w = 0 → ∃ w₀ ∈ D₀.Z, F.onPol w₀ = (l : K) ^ n • w) := by
  first | exact @GlobalTheory.exactTriple_jumps_chars_lift | exact GlobalTheory.exactTriple_jumps_chars_lift | (intros; apply GlobalTheory.exactTriple_jumps_chars_lift <;> assumption)
