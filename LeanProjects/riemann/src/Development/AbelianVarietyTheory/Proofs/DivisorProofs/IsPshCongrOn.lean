import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

namespace GlobalTheory

open Metric

theorem isPsh_congr_on (D : ℕ) (U : Set (Fin D → ℂ)) (φ ψ : (Fin D → ℂ) → ℝ)
    (hφ : ReciprocityTheory.AnForm.A.IsPsh U φ) (h : ∀ z ∈ U, φ z = ψ z) :
    ReciprocityTheory.AnForm.A.IsPsh U ψ := by
  obtain ⟨husc, hmean⟩ := hφ
  refine ⟨fun x hx => UpperSemicontinuousWithinAt.congr_of_eventuallyEq (f := φ) (g := ψ)
    (husc x hx) hx (eventually_nhdsWithin_of_forall h), fun z w hdisc => ?_⟩
  obtain ⟨hint, hle⟩ := hmean z w hdisc
  have heq : Set.EqOn (fun ζ : ℂ => φ (z + ζ • w)) (fun ζ : ℂ => ψ (z + ζ • w))
      (sphere (0 : ℂ) |(1 : ℝ)|) := by
    intro ζ hζ
    have hn : ‖ζ‖ = 1 := by simpa using hζ
    exact h _ (hdisc ζ hn.le)
  have hz : z ∈ U := by simpa using hdisc 0 (by simp)
  refine ⟨(circleIntegrable_congr heq).1 hint, ?_⟩
  rw [← h z hz, ← Real.circleAverage_congr_sphere heq]
  exact hle

end GlobalTheory
