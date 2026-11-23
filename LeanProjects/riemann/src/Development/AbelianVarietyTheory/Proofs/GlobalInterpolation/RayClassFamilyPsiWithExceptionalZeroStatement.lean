import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyPsiWithExceptionalZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassFamily_psi_with_exceptional_zero : ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 20 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (Z : Finset ℝ) (u : ℝ), 𝓕.ExcZ χ c₀ Z → 2 ≤ u → Real.log 𝓕.B ≤ Real.sqrt (Real.log u) → ‖𝓕.psi χ u - (if χ = 1 then (u : ℂ) else 0) + ∑ β ∈ Z, (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u)) := by
  first | exact @GlobalTheory.Hk.PsiExc.psi_exceptional | exact GlobalTheory.Hk.PsiExc.psi_exceptional | (intros; apply GlobalTheory.Hk.PsiExc.psi_exceptional <;> assumption)
